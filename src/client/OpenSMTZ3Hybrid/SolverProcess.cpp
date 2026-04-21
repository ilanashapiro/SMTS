/*
 * Hybrid SMTS backend:
 * - OpenSMT (SplitterInterpret) handles partitioning and lemma production.
 * - Z3 runs as a subprocess, receiving SMT-LIB2 via pipe, for solving.
 *
 * Isolating Z3 into its own process prevents mutex deadlocks caused by
 * fork()-ing a process that holds a live z3::context.  Z3's incremental
 * state (push/pop/assert stack) is maintained across cubes because the
 * subprocess persists for the lifetime of the worker.
 *
 * Lemma sharing works correctly: OpenSMT serialises learned clauses via
 * removeAuxVars() + dumpWithLets(), producing standard SMT-LIB2 over
 * the original theory atoms, which Z3 can assert directly.
 */

#include "client/SolverProcess.h"
#include "lib/net/Report.h"
#include "lib/Logger.h"

#include <parallel/SplitterInterpret.h>
#include <common/ReportUtils.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <csignal>
#include <iostream>
#include <cctype>
#include <string>
#include <vector>

#ifdef __linux__
#include <sys/prctl.h>
#endif

using opensmt::SMTConfig;
using opensmt::SMTOption;
using opensmt::sstat;
using opensmt::s_True;
using opensmt::s_False;
using opensmt::s_Undef;
using opensmt::s_Error;
using opensmt::parallel::SplitterInterpret;
using opensmt::parallel::MainSplitter;
using opensmt::parallel::ScatterSplitter;

std::string SolverProcess::solver = "OpenSMTZ3";

static SplitterInterpret *   splitterInterpret = nullptr;
static SMTConfig *           config            = nullptr;
static sstat                 result;
static std::string           base_instance;
static SolverProcess::Result z3_last_result = SolverProcess::Result::UNKNOWN;

// ── Z3 subprocess ────────────────────────────────────────────────────────────

struct Z3Proc {
    pid_t pid       = -1;
    int   stdin_fd  = -1;      // parent writes SMT-LIB2 here → Z3's stdin
    int   stdout_fd = -1;      // raw fd for fork-child detach
    FILE* stdout_fp = nullptr; // parent reads results here  ← Z3's stdout

    bool valid() const { return pid > 0; }
};

static Z3Proc z3proc;

static bool z3_send(const std::string & cmd) {
    if (!z3proc.valid()) return false;
    const char * s = cmd.c_str();
    size_t rem     = cmd.size();
    while (rem > 0) {
        ssize_t n = write(z3proc.stdin_fd, s, rem);
        if (n <= 0) return false;
        s += n; rem -= n;
    }
    return true;
}

static SolverProcess::Result z3_read_result() {
    if (!z3proc.stdout_fp) return SolverProcess::Result::ERROR;
    char buf[64] = {};
    if (!fgets(buf, sizeof(buf), z3proc.stdout_fp))
        return SolverProcess::Result::ERROR;
    size_t len = strlen(buf);
    while (len > 0 && (buf[len-1] == '\n' || buf[len-1] == '\r' || buf[len-1] == ' '))
        buf[--len] = '\0';
    if (strcmp(buf, "sat")   == 0) return SolverProcess::Result::SAT;
    if (strcmp(buf, "unsat") == 0) return SolverProcess::Result::UNSAT;
    if (strncmp(buf, "(error", 6) == 0) return SolverProcess::Result::ERROR;
    return SolverProcess::Result::UNKNOWN;
}

static bool launch_z3() {
    int to_z3[2], from_z3[2];
    if (pipe(to_z3) < 0) return false;
    if (pipe(from_z3) < 0) {
        close(to_z3[0]);
        close(to_z3[1]);
        return false;
    }

    pid_t pid = fork();
    if (pid < 0) {
        close(to_z3[0]);  close(to_z3[1]);
        close(from_z3[0]); close(from_z3[1]);
        return false;
    }
    if (pid == 0) {
        // child — become the Z3 process
#ifdef __linux__
        prctl(PR_SET_PDEATHSIG, SIGKILL);
#endif
        dup2(to_z3[0],   STDIN_FILENO);
        dup2(from_z3[1], STDOUT_FILENO);
        close(to_z3[0]);  close(to_z3[1]);
        close(from_z3[0]); close(from_z3[1]);
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull >= 0) { dup2(devnull, STDERR_FILENO); close(devnull); }
        execlp("z3", "z3", "-in", (char*)nullptr);
        _exit(1); // exec failed
    }
    // parent — keep our ends only
    close(to_z3[0]);
    close(from_z3[1]);
    z3proc.pid       = pid;
    z3proc.stdin_fd  = to_z3[1];
    z3proc.stdout_fd = from_z3[0];
    z3proc.stdout_fp = fdopen(from_z3[0], "r");
    if (!z3proc.stdout_fp) {
        close(to_z3[1]);
        close(from_z3[0]);
        kill(pid, SIGKILL);
        waitpid(pid, nullptr, 0);
        z3proc = Z3Proc{};
        return false;
    }

    struct sigaction ignore_pipe;
    memset(&ignore_pipe, 0, sizeof(ignore_pipe));
    ignore_pipe.sa_handler = SIG_IGN;
    sigaction(SIGPIPE, &ignore_pipe, nullptr);

    return true;
}

static void kill_z3() {
    if (!z3proc.valid()) return;
    z3_send("(exit)\n");
    close(z3proc.stdin_fd);
    if (z3proc.stdout_fp) fclose(z3proc.stdout_fp);
    kill(z3proc.pid, SIGKILL);
    waitpid(z3proc.pid, nullptr, 0);
    z3proc = Z3Proc{};
}

// Called inside the partition() fork-child to release inherited pipe FDs
// without disturbing the parent's connection to Z3.
static void detach_z3_in_child() {
    if (!z3proc.valid()) return;
    if (z3proc.stdin_fd >= 0) close(z3proc.stdin_fd);
    if (z3proc.stdout_fd >= 0) close(z3proc.stdout_fd);
    z3proc = Z3Proc{}; // child does not own Z3
}

// ── SMT-LIB2 command splitter (unchanged) ───────────────────────────────────

static std::vector<std::string> splitTopLevelCommands(std::string const & script) {
    std::vector<std::string> commands;
    int depth = 0;
    size_t start = std::string::npos;
    bool inString = false;
    bool inQuotedSymbol = false;
    bool inComment = false;

    for (size_t i = 0; i < script.size(); ++i) {
        char c = script[i];
        if (inComment) {
            if (c == '\n') inComment = false;
            continue;
        }
        if (!inString && !inQuotedSymbol && c == ';') { inComment = true; continue; }
        if (!inQuotedSymbol && c == '"') { inString = !inString; continue; }
        if (!inString && c == '|') { inQuotedSymbol = !inQuotedSymbol; continue; }
        if (inString || inQuotedSymbol) continue;
        if (c == '(') {
            if (depth == 0) start = i;
            ++depth;
        } else if (c == ')') {
            --depth;
            if (depth == 0 && start != std::string::npos) {
                commands.push_back(script.substr(start, i - start + 1));
                start = std::string::npos;
            }
        }
    }
    return commands;
}

static bool isCommand(std::string const & command, char const * expected) {
    size_t i = 0;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i]))) ++i;
    if (i == command.size() || command[i] != '(') return false;
    ++i;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i]))) ++i;
    size_t begin = i;
    while (i < command.size() && !std::isspace(static_cast<unsigned char>(command[i])) && command[i] != ')') ++i;
    return command.compare(begin, i - begin, expected) == 0;
}

static unsigned commandArgumentOrOne(std::string const & command) {
    size_t i = 0;
    while (i < command.size() && command[i] != '(') ++i;
    if (i < command.size()) ++i;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i]))) ++i;
    while (i < command.size() && !std::isspace(static_cast<unsigned char>(command[i])) && command[i] != ')') ++i;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i]))) ++i;
    if (i == command.size() || command[i] == ')') return 1;
    return static_cast<unsigned>(std::stoul(command.substr(i)));
}

// ── Z3 subprocess communication ──────────────────────────────────────────────

// Forward SMT-LIB2 commands from script to the Z3 subprocess, translating
// push/pop structurally and skipping solve/query commands.
static bool applyZ3Subprocess(net::Socket const & socket,
                               PTPLib::net::SMTS_Event & event,
                               std::string const & script) {
    for (std::string const & command : splitTopLevelCommands(script)) {
        if (isCommand(command, "check-sat")     ||
            isCommand(command, "exit")          ||
            isCommand(command, "get-model")     ||
            isCommand(command, "get-value")     ||
            isCommand(command, "get-info")      ||
            isCommand(command, "get-unsat-core")) {
            continue;
        }
        if (!z3_send(command + "\n")) {
            net::Report::error(socket, event.header, "Z3 subprocess write error");
            return false;
        }
    }
    return true;
}

static void configureZ3(net::Socket const & socket,
                        PTPLib::net::SMTS_Event & event) {
    std::string seed = event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SEED);
    if (!seed.empty()) {
        // set-option must precede set-logic; init() calls this before applyZ3Subprocess
        if (!z3_send("(set-option :random-seed " + seed + ")\n"))
            net::Report::warning(socket, event.header, "Z3 subprocess: failed to set random-seed");
    }
}

// ── OpenSMT helpers (unchanged) ──────────────────────────────────────────────

static opensmt::vec<opensmt::pair<int,int>> extractSolverBranch(std::string solverBranch_str) {
    opensmt::vec<opensmt::pair<int,int>> solverBranch;
    solverBranch_str.erase(std::remove(solverBranch_str.begin(), solverBranch_str.end(), ' '), solverBranch_str.end());
    std::string const delimiter = ",";
    size_t beg, pos = 0;
    int counter = 0, temp = 0;
    while ((beg = solverBranch_str.find_first_not_of(delimiter, pos)) != std::string::npos) {
        pos = solverBranch_str.find_first_of(delimiter, beg + 1);
        int index = stoi(solverBranch_str.substr(beg, pos - beg));
        if (counter % 2 == 1) solverBranch.push({temp, index});
        else temp = index;
        counter++;
    }
    return solverBranch;
}

static opensmt::vec<opensmt::pair<int,int>> eventBranch(PTPLib::net::SMTS_Event const & event) {
    return extractSolverBranch(event.header.at(PTPLib::common::Param.NODE).substr(
        1, event.header.at(PTPLib::common::Param.NODE).size() - 2));
}

inline MainSplitter & getMainSplitter() {
    return dynamic_cast<MainSplitter&>(splitterInterpret->getMainSolver());
}

inline ScatterSplitter & getScatterSplitter() {
    return dynamic_cast<ScatterSplitter&>(getMainSplitter().getSMTSolver());
}

// ── SolverProcess interface ──────────────────────────────────────────────────

SolverProcess::Result SolverProcess::init(PTPLib::net::SMTS_Event & SMTS_Event) {
    const char * msg;
    static const char * default_split = SMTConfig::o_sat_scatter_split;

    if (SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE).size() > 0 &&
        SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE) != SMTConfig::o_sat_lookahead_split &&
        SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE) != SMTConfig::o_sat_scatter_split)
    {
        net::Report::warning(get_SMTS_socket(), SMTS_Event.header,
            "bad parameter.split-type: '" +
            SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SEED) +
            "'. using default (" + default_split + ")");
    }
    if (SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE).empty())
        SMTS_Event.header.set(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE, default_split);

    config = new SMTConfig();
    if (!config)
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";SMTConfig: out of memory");

    config->setRandomSeed(atoi(SMTS_Event.header.get(PTPLib::net::parameter, "seed").c_str()));
    config->setOption(SMTConfig::o_sat_scatter_split,
        SMTOption(SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE).c_str()), msg);
    if (SMTS_Event.header.count(PTPLib::common::Param.SPLIT_PREFERENCE))
        config->setOption(SMTConfig::o_sat_split_preference,
            SMTOption(SMTS_Event.header.at(PTPLib::common::Param.SPLIT_PREFERENCE).c_str()), msg);
    config->setOption(SMTConfig::o_sat_split_units,    SMTOption(opensmt::spts_search_counter), msg);
    config->setOption(SMTConfig::o_sat_split_inittune, SMTOption(INT_MAX), msg);

    splitterInterpret = new SplitterInterpret(*config, getChannel());
    if (!splitterInterpret)
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";SplitterInterpret: out of memory");

    // Launch Z3 subprocess before loading the formula so random-seed is set first.
    if (!launch_z3()) {
        net::Report::error(get_SMTS_socket(), SMTS_Event.header, "failed to launch Z3 subprocess");
        return SolverProcess::Result::ERROR;
    }
    configureZ3(get_SMTS_socket(), SMTS_Event);

    if (log_enabled) {
        base_instance = SMTS_Event.body;
        Logger::build_SolverInputPath(true, true,
            "(set-option :random-seed " + SMTS_Event.header.get(PTPLib::net::parameter, "seed") + ")\n" +
            "(set-option :split-units time)\n" +
            "(set-option :split-init-tune " + std::to_string(DBL_MAX) + ")",
            to_string(get_SMTS_socket().get_local()), getpid());
    }

    auto res = splitterInterpret->interpSMTContent(
        (char *) SMTS_Event.body.c_str(), eventBranch(SMTS_Event), false, false);
    if (res == s_Error) return SolverProcess::Result::ERROR;

    if (!applyZ3Subprocess(get_SMTS_socket(), SMTS_Event, SMTS_Event.body))
        return SolverProcess::Result::ERROR;

    if (log_enabled)
        getScatterSplitter().set_syncedStream(synced_stream);

    return SolverProcess::Result::UNKNOWN;
}

void SolverProcess::cleanSolverState() {
    kill_z3();
    z3_last_result = SolverProcess::Result::UNKNOWN;
    delete config;         config = nullptr;
    delete splitterInterpret; splitterInterpret = nullptr;
    result = s_Undef;
}

SolverProcess::Result SolverProcess::solve(PTPLib::net::SMTS_Event SMTS_event, bool shouldUpdateSolverBranch) {
    result = s_Undef;
    z3_last_result = SolverProcess::Result::UNKNOWN;
    getScatterSplitter().resetSplitType();

    if (log_enabled) {
        synced_stream.println(log_enabled ? PTPLib::common::Color::FG_Green : PTPLib::common::Color::FG_DEFAULT,
            "[t SEARCH ] -> ", "CURRENT SOLVER BRANCH: ",
            SMTS_event.header.at(PTPLib::common::Param.NODE),
            " QUERY: ", SMTS_event.header.at(PTPLib::common::Param.QUERY));
        synced_stream.println(log_enabled ? PTPLib::common::Color::FG_Green : PTPLib::common::Color::FG_DEFAULT,
            "[t SEARCH ] -> ", "SMT2 SCRIPT: ",
            SMTS_event.body + SMTS_event.header.at(PTPLib::common::Param.QUERY));
    }
    assert(not SMTS_event.header.at(PTPLib::common::Param.QUERY).empty());

    if (SMTS_event.header.at(PTPLib::common::Param.COMMAND) == PTPLib::common::Command.INCREMENTAL) {
        auto res = splitterInterpret->interpSMTContent(
            (char *) SMTS_event.body.c_str(),
            eventBranch(SMTS_event), shouldUpdateSolverBranch, true);
        if (res == s_Error) return SolverProcess::Result::ERROR;

        if (!applyZ3Subprocess(get_SMTS_socket(), SMTS_event, SMTS_event.body))
            return SolverProcess::Result::ERROR;
    }

    if (log_enabled) {
        Logger::build_SolverInputPath(false, true,
            base_instance + "\n" + SMTS_event.body + "\n" +
            SMTS_event.header.at(PTPLib::common::Param.QUERY),
            to_string(get_SMTS_socket().get_local()), getpid());
        base_instance.clear();
    }

    if (!z3_send("(check-sat)\n")) {
        net::Report::error(get_SMTS_socket(), SMTS_event.header, "Z3 subprocess write error during check-sat");
        return SolverProcess::Result::ERROR;
    }
    z3_last_result = z3_read_result();
    return z3_last_result;
}

volatile sig_atomic_t shutdown_flag = 1;
void cleanupRoutine(int) { shutdown_flag = 0; }

void SolverProcess::partition(PTPLib::net::SMTS_Event & SMTS_Event, uint8_t n) {
    if (z3_last_result != SolverProcess::Result::UNKNOWN) return;
    if (getMainSplitter().getStatus() != s_Undef) return;

    forked_partitionId = fork();
    if (forked_partitionId == -1) { perror("fork"); exit(EXIT_FAILURE); }
    if (forked_partitionId > 0)  { forked = true; return; }

    // ── partition child ──────────────────────────────────────────────────────
    // Detach from Z3 pipes immediately: child only uses OpenSMT.
    detach_z3_in_child();

    if (!log_enabled) {
        FILE * file = fopen("/dev/null", "w");
        dup2(fileno(file), fileno(stdout));
        dup2(fileno(file), fileno(stderr));
        fclose(file);
    }

    std::thread t_handle_orphan([&] {
        while (true) { sleep(1); if (getppid() == 1) exit(EXIT_SUCCESS); }
    });

    struct sigaction sigterm_action;
    memset(&sigterm_action, 0, sizeof(sigterm_action));
    sigterm_action.sa_handler = &cleanupRoutine;
    sigterm_action.sa_flags   = 0;
    if (sigfillset(&sigterm_action.sa_mask) != 0) { perror("sigfillset"); exit(EXIT_FAILURE); }
    if (sigaction(SIGTERM, &sigterm_action, nullptr) != 0) { perror("sigaction"); exit(EXIT_FAILURE); }

    getChannel().clearClauseShareMode();
    std::vector<std::string> partitions;
    int searchCounter = ((ScatterSplitter &) getMainSplitter().getSMTSolver()).getSearchCounter();
    std::string statusInfo = getMainSplitter().getConfig().getInfo(":status").toString();
    const char * msg;

    if (!(getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_num,      SMTOption(int(n)), msg) &&
          getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_units,    SMTOption(opensmt::spts_search_counter), msg) &&
          getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_inittune, SMTOption(1), msg) &&
          getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_midtune,  SMTOption(1), msg)))
    {
        net::Report::report(get_SMTS_socket(), partitions, to_string(searchCounter), statusInfo, SMTS_Event, msg);
    } else {
        try {
            getScatterSplitter().setSplitTypeScatter();
            sstat status = getMainSplitter().solve();
            if (status == s_Undef || status == s_False) {
                partitions = getMainSplitter().getPartitionClauses();
                net::Report::report(get_SMTS_socket(), partitions, to_string(searchCounter), statusInfo, SMTS_Event);
            } else if (status == s_True) {
                synced_stream.println_bold(log_enabled ? PTPLib::common::Color::FG_Red : PTPLib::common::Color::FG_DEFAULT,
                    "[ t ", __func__, "] -> ", " Partition Report sat ",
                    SMTS_Event.header.at(PTPLib::common::Param.NODE));
                net::Report::report(get_SMTS_socket(), SMTS_Event.header, SolverProcess::resultToString(Result::SAT));
            } else {
                net::Report::report(get_SMTS_socket(), partitions, to_string(searchCounter), statusInfo, SMTS_Event,
                    "error during partitioning");
            }
        } catch (std::exception & ex) {
            net::Report::error(get_SMTS_socket(), SMTS_Event.header, std::string(ex.what()));
            exit(EXIT_FAILURE);
        }
    }

    if (log_enabled) {
        fprintf(stdout, "; ============================[ Partition Statistics ]=======================================\n");
        fprintf(stdout, "; | SearchCounter |  SplitType  |  Child PID  |  Time  |  MEM USAGE |\n");
        reportf("; %9d   | %8d    |   %8d  |  %8.3f s  | %6.3f MB\n",
            searchCounter, getScatterSplitter().getSplitTypeValue(),
            getpid(), opensmt::cpuTime(), opensmt::memUsed() / 1048576.0);
        fflush(stdout);
    }
    exit(EXIT_SUCCESS);
}

void SolverProcess::kill_partition_process() {
    int wstatus;
    if (kill(forked_partitionId, SIGKILL) == -1) { perror("kill"); exit(EXIT_FAILURE); }
    if (waitpid(forked_partitionId, &wstatus, WUNTRACED | WCONTINUED) == -1) { perror("waitpid"); exit(EXIT_FAILURE); }
}

void SolverProcess::add_constraint(std::unique_ptr<PTPLib::net::map_solverBranch_lemmas> const & clauses,
                                   std::string & branch) {
    for (auto const & lemmaPulled : *clauses) {
        if (log_enabled)
            synced_stream.println(log_enabled ? PTPLib::common::Color::FG_Cyan : PTPLib::common::Color::FG_DEFAULT,
                "[ t ", __func__, "] -> ", " check for Node -> " + lemmaPulled.first);
        if (!lemmaPulled.first.empty()) {
            assert(!lemmaPulled.first.empty() && !branch.empty());
            if (isPrefix(lemmaPulled.first.substr(1, lemmaPulled.first.size() - 2),
                         branch.substr(1, branch.size() - 2))) {
                if (log_enabled)
                    synced_stream.println_bold(log_enabled ? PTPLib::common::Color::FG_Cyan : PTPLib::common::Color::FG_DEFAULT,
                        "[ t ", __func__, "] -> ", "Solver At: ", branch,
                        " Injecting ", lemmaPulled.second.size(), " Clauses From: ", lemmaPulled.first);

                for (auto const & lemma : lemmaPulled.second) {
                    assert(lemma.clause.size());
                    if (log_enabled)
                        synced_stream.println(log_enabled ? PTPLib::common::Color::FG_Cyan : PTPLib::common::Color::FG_DEFAULT,
                            lemma.clause);

                    // Lemmas are already SMT-LIB2 (OpenSMT serialises via
                    // removeAuxVars + dumpWithLets before storing in the channel).
                    std::string assertion = "(assert " + lemma.clause + ")\n";
                    splitterInterpret->interpFile((char *) assertion.c_str());
                    if (!z3_send(assertion)) {
                        PTPLib::net::Header header;
                        net::Report::warning(get_SMTS_socket(), header, "Z3 subprocess write error during lemma injection");
                    }
                }
            }
        }
    }
}

void SolverProcess::getCnfClauses(PTPLib::net::SMTS_Event & smtsEvent) {
    if (smtsEvent.header.count(PTPLib::common::Param.QUERY)) {
        pid_t pid = getpid();
        if (fork() != 0) return;
        detach_z3_in_child();
        std::thread _t([&] { while (getppid() == pid) { sleep(1); } exit(0); });
        SMTConfig config;
        config.set_dryrun(true);
        splitterInterpret = new SplitterInterpret(config, getChannel());
        if (!splitterInterpret)
            throw PTPLib::common::Exception(__FILE__, __LINE__, ";SplitterInterpret: out of memory");
        splitterInterpret->interpFile((char *) (smtsEvent.body + smtsEvent.header[PTPLib::common::Param.QUERY]).c_str());
        std::string cnf = getMainSplitter().getSMTSolver().printCnfClauses();
        net::Report::report(get_SMTS_socket(), smtsEvent.header, smtsEvent.header[PTPLib::common::Param.COMMAND], cnf);
        exit(0);
    } else {
        std::string cnf = getMainSplitter().getSMTSolver().printCnfClauses();
        net::Report::report(get_SMTS_socket(), smtsEvent.header, smtsEvent.header[PTPLib::common::Param.COMMAND], cnf);
    }
}

void SolverProcess::getCnfLearnts(PTPLib::net::Header & header) {
    std::string cnf = getMainSplitter().getSMTSolver().printCnfLearnts();
    net::Report::report(get_SMTS_socket(), header, header[PTPLib::common::Param.COMMAND], cnf);
}
