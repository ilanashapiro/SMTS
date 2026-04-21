/*
 * Hybrid SMTS backend:
 * - OpenSMT owns the partitioning state and produces partition clauses.
 * - Z3 owns the solving state and reports sat/unsat/unknown.
 *
 * The two states receive the same incremental assertion-stack updates from
 * SMTS.  This preserves the solver relocation semantics described by SMTS:
 * moving down the partition tree is a push/assert, moving up is a pop.
 */

#include "client/SolverProcess.h"
#include "lib/net/Report.h"
#include "lib/Logger.h"

#include <parallel/SplitterInterpret.h>
#include <common/ReportUtils.h>

#include "z3++.h"

#include <cstdio>
#include <cstdlib>
#include <unistd.h>
#include <sys/wait.h>
#include <csignal>
#include <iostream>
#include <memory>
#include <cctype>

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

SplitterInterpret *         splitterInterpret;
SMTConfig    *              config;
sstat                       result;
std::string                 base_instance;
SolverProcess::Result       z3_last_result = SolverProcess::Result::UNKNOWN;

struct Z3State {
    z3::context context;
    z3::solver solver;

    Z3State() : solver(context) {}
};

std::unique_ptr<Z3State> z3State;

inline MainSplitter & getMainSplitter() {
    return dynamic_cast<MainSplitter&>(splitterInterpret->getMainSolver());
};

inline ScatterSplitter & getScatterSplitter() {
    return dynamic_cast<ScatterSplitter&>(getMainSplitter().getSMTSolver());
}

opensmt::vec<opensmt::pair<int,int>> extractSolverBranch(std::string solverBranch_str)
{
    opensmt::vec<opensmt::pair<int,int>> solverBranch;
    solverBranch_str.erase(std::remove(solverBranch_str.begin(), solverBranch_str.end(), ' '), solverBranch_str.end());
    std::string const delimiter = ",";
    size_t beg, pos = 0;
    int counter = 0;
    int temp = 0;
    while ((beg = solverBranch_str.find_first_not_of(delimiter, pos)) != std::string::npos)
    {
        pos = solverBranch_str.find_first_of(delimiter, beg + 1);
        int index = stoi(solverBranch_str.substr(beg, pos - beg));
        if (counter % 2 == 1) {
            solverBranch.push({temp, index});
        } else temp = index;
        counter++;
    }
    return solverBranch;
}

static opensmt::vec<opensmt::pair<int,int>> eventBranch(PTPLib::net::SMTS_Event const & event) {
    return extractSolverBranch(event.header.at(PTPLib::common::Param.NODE).substr(
            1, event.header.at(PTPLib::common::Param.NODE).size() - 2));
}

static SolverProcess::Result z3ResultToSMTS(z3::check_result res) {
    if (res == z3::sat)
        return SolverProcess::Result::SAT;
    if (res == z3::unsat)
        return SolverProcess::Result::UNSAT;
    return SolverProcess::Result::UNKNOWN;
}

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
            if (c == '\n')
                inComment = false;
            continue;
        }
        if (!inString && !inQuotedSymbol && c == ';') {
            inComment = true;
            continue;
        }
        if (!inQuotedSymbol && c == '"') {
            inString = !inString;
            continue;
        }
        if (!inString && c == '|') {
            inQuotedSymbol = !inQuotedSymbol;
            continue;
        }
        if (inString || inQuotedSymbol)
            continue;
        if (c == '(') {
            if (depth == 0)
                start = i;
            ++depth;
        }
        else if (c == ')') {
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
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i])))
        ++i;
    if (i == command.size() || command[i] != '(')
        return false;
    ++i;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i])))
        ++i;
    size_t begin = i;
    while (i < command.size() && !std::isspace(static_cast<unsigned char>(command[i])) && command[i] != ')')
        ++i;
    return command.compare(begin, i - begin, expected) == 0;
}

static unsigned commandArgumentOrOne(std::string const & command) {
    size_t i = 0;
    while (i < command.size() && command[i] != '(')
        ++i;
    if (i < command.size())
        ++i;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i])))
        ++i;
    while (i < command.size() && !std::isspace(static_cast<unsigned char>(command[i])) && command[i] != ')')
        ++i;
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i])))
        ++i;
    if (i == command.size() || command[i] == ')')
        return 1;
    return static_cast<unsigned>(std::stoul(command.substr(i)));
}

static bool applyZ3SMT2(net::Socket const & socket, PTPLib::net::SMTS_Event & event, std::string const & script) {
    for (std::string const & command : splitTopLevelCommands(script)) {
        try {
            if (isCommand(command, "push")) {
                unsigned n = commandArgumentOrOne(command);
                for (unsigned i = 0; i < n; ++i)
                    z3State->solver.push();
            }
            else if (isCommand(command, "pop")) {
                z3State->solver.pop(commandArgumentOrOne(command));
            }
            else if (isCommand(command, "check-sat") || isCommand(command, "exit") ||
                     isCommand(command, "get-model") || isCommand(command, "get-value") ||
                     isCommand(command, "get-info") || isCommand(command, "get-unsat-core")) {
                continue;
            }
            else {
                z3State->solver.from_string(command.c_str());
            }
        }
        catch (z3::exception & ex) {
            net::Report::error(socket, event.header, std::string("Z3 parser error: ") + ex.msg());
            return false;
        }
        catch (std::exception & ex) {
            net::Report::error(socket, event.header, std::string("Z3 parser error: ") + ex.what());
            return false;
        }
    }
    return true;
}

static void configureZ3(PTPLib::net::SMTS_Event const & event) {
    z3::params params(z3State->context);
    std::string seed = event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SEED);
    if (!seed.empty())
        params.set("random_seed", static_cast<unsigned>(std::stoul(seed)));
    z3State->solver.set(params);
}

SolverProcess::Result SolverProcess::init(PTPLib::net::SMTS_Event & SMTS_Event) {
    const char *msg;
    static const char *default_split = SMTConfig::o_sat_scatter_split;

    if (SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE).size() > 0 and
            SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE) != SMTConfig::o_sat_lookahead_split and
            SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE) != SMTConfig::o_sat_scatter_split)
    {
        net::Report::warning(get_SMTS_socket(), SMTS_Event.header,"bad parameter.split-type: '" +
            SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SEED) + "'. using default (" + default_split +")");
    }
    if (SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE).size() == 0) {
        SMTS_Event.header.set(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE, default_split);
    }

    if ( not (config = new SMTConfig()))
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";SMTConfig: out of memory");

    config->setRandomSeed(atoi(SMTS_Event.header.get(PTPLib::net::parameter, "seed").c_str()));
    config->setOption(SMTConfig::o_sat_scatter_split,
                     SMTOption(SMTS_Event.header.get(PTPLib::net::parameter, PTPLib::common::Param.SPLIT_TYPE).c_str()), msg);
    if (SMTS_Event.header.count(PTPLib::common::Param.SPLIT_PREFERENCE)) {
        config->setOption(SMTConfig::o_sat_split_preference, SMTOption(SMTS_Event.header.at(PTPLib::common::Param.SPLIT_PREFERENCE).c_str()), msg);
    }
    config->setOption(SMTConfig::o_sat_split_units, SMTOption(opensmt::spts_search_counter), msg);
    config->setOption(SMTConfig::o_sat_split_inittune, SMTOption(INT_MAX), msg);

    if (not (splitterInterpret = new SplitterInterpret(*config, getChannel())))
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";SplitterInterpret: out of memory");

    z3State.reset(new Z3State());
    configureZ3(SMTS_Event);

    if (log_enabled) {
        base_instance = SMTS_Event.body;
        Logger::build_SolverInputPath(true, true, "(set-option :random-seed " +
                                                  SMTS_Event.header.get(PTPLib::net::parameter, "seed") + ")"
                                                                                                          "\n" +
                                                  std::string("(set-option :split-units time)") + "\n" + std::string(
                "(set-option :split-init-tune " + to_string(DBL_MAX) + ")"),
                                      to_string(get_SMTS_socket().get_local()), getpid());
    }

    auto res = splitterInterpret->interpSMTContent((char *) SMTS_Event.body.c_str(), eventBranch(SMTS_Event), false, false);
    if (res == s_Error)
        return SolverProcess::Result::ERROR;

    if (!applyZ3SMT2(get_SMTS_socket(), SMTS_Event, SMTS_Event.body))
        return SolverProcess::Result::ERROR;

    if (log_enabled)
        getScatterSplitter().set_syncedStream(synced_stream);

    return SolverProcess::Result::UNKNOWN;
}

void SolverProcess::cleanSolverState() {
    z3State.reset();
    z3_last_result = SolverProcess::Result::UNKNOWN;
    delete config;
    config = nullptr;
    delete splitterInterpret;
    splitterInterpret = nullptr;
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
        auto res = splitterInterpret->interpSMTContent((char *) SMTS_event.body.c_str(),
                                                       eventBranch(SMTS_event),
                                                       shouldUpdateSolverBranch,
                                                       true);
        if (res == s_Error)
            return SolverProcess::Result::ERROR;

        if (!applyZ3SMT2(get_SMTS_socket(), SMTS_event, SMTS_event.body))
            return SolverProcess::Result::ERROR;
    }

    if (log_enabled) {
        Logger::build_SolverInputPath(false, true,
                                      base_instance + "\n" + SMTS_event.body + "\n" +
                                      SMTS_event.header.at(PTPLib::common::Param.QUERY),
                                      to_string(get_SMTS_socket().get_local()), getpid());
        base_instance.clear();
    }

    try {
        z3_last_result = z3ResultToSMTS(z3State->solver.check());
        return z3_last_result;
    }
    catch (z3::exception & ex) {
        net::Report::error(get_SMTS_socket(), SMTS_event.header, std::string("Z3 check error: ") + ex.msg());
        return SolverProcess::Result::ERROR;
    }
}

volatile sig_atomic_t shutdown_flag = 1;
void cleanupRoutine(int signal_number) {
    shutdown_flag = 0;
}

void SolverProcess::partition(PTPLib::net::SMTS_Event & SMTS_Event, uint8_t n) {
    if (z3_last_result != SolverProcess::Result::UNKNOWN) return;
    if (getMainSplitter().getStatus() != s_Undef) return;

    forked_partitionId = fork();
    if (forked_partitionId == -1) {
        perror("fork");
        exit(EXIT_FAILURE);
    }
    if (forked_partitionId > 0) {
        forked = true;
        return;
    }
    if (not log_enabled) {
        FILE * file = fopen("/dev/null", "w");
        dup2(fileno(file), fileno(stdout));
        dup2(fileno(file), fileno(stderr));
        fclose(file);
    }
    std::thread t_handle_orphant([&] {
        while (true) {
            sleep(1);
            if (getppid() == 1)
                exit(EXIT_SUCCESS);
        }
    });

    struct sigaction sigterm_action;
    memset(&sigterm_action, 0, sizeof(sigterm_action));
    sigterm_action.sa_handler = &cleanupRoutine;
    sigterm_action.sa_flags = 0;

    if (sigfillset(&sigterm_action.sa_mask) != 0)
    {
        perror("sigfillset");
        exit(EXIT_FAILURE);
    }
    if (sigaction(SIGTERM, &sigterm_action, NULL) != 0)
    {
        perror("sigaction SIGTERM");
        exit(EXIT_FAILURE);
    }
    getChannel().clearClauseShareMode();
    std::vector<std::string> partitions;
    int searchCounter = (((ScatterSplitter &) getMainSplitter().getSMTSolver()).getSearchCounter());
    std::string statusInfo = getMainSplitter().getConfig().getInfo(":status").toString();
    const char *msg;
    if ( not (
            getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_num, SMTOption(int(n)),msg)                   and
            getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_units, SMTOption(opensmt::spts_search_counter), msg)   and
            getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_inittune, SMTOption(1), msg)         and
            getMainSplitter().getConfig().setOption(SMTConfig::o_sat_split_midtune, SMTOption(1), msg)
             )
        )
    {
        net::Report::report(get_SMTS_socket(), partitions, to_string(searchCounter), statusInfo, SMTS_Event, msg);
    }
    else {
        try {
            getScatterSplitter().setSplitTypeScatter();
            sstat status = getMainSplitter().solve();
            if (status == s_Undef or status == s_False) {
                partitions = getMainSplitter().getPartitionClauses();
                net::Report::report(get_SMTS_socket(), partitions, to_string(searchCounter), statusInfo, SMTS_Event);
            }
            else if (status == s_True) {
                synced_stream.println_bold(log_enabled ? PTPLib::common::Color::FG_Red : PTPLib::common::Color::FG_DEFAULT,
                                           "[ t ", __func__, "] -> ", " Partition Report sat ", SMTS_Event.header.at(PTPLib::common::Param.NODE));
                net::Report::report(get_SMTS_socket(), SMTS_Event.header, SolverProcess::resultToString( Result::SAT));
            }
            else {
                net::Report::report(get_SMTS_socket(), partitions, to_string(searchCounter), statusInfo, SMTS_Event, "error during partitioning");
            }
        }
        catch (std::exception & ex)
        {
            net::Report::error(get_SMTS_socket(), SMTS_Event.header, std::string(ex.what()));
            exit(EXIT_FAILURE);
        }
    }
    if (log_enabled) {
        fprintf(stdout,
                "; ============================[ Partition Statistics ]=================================================\n");
        fprintf(stdout,
                "; | SearchCounter |          SplitType         |          Child Process ID    | Time     | MEM USAGE | \n");
        fprintf(stdout,
                "; |           |                            |                              |          |           | \n");
        reportf("; %9d   | %8d                %8d           |           %8.3f s      | %6.3f MB\n", searchCounter,
                getScatterSplitter().getSplitTypeValue(), getpid(), opensmt::cpuTime(), opensmt::memUsed() / 1048576.0);
        fflush(stderr);
        fprintf(stdout,
                "; =====================================================================================================\n");
    }
    exit(EXIT_SUCCESS);
}

void SolverProcess::kill_partition_process()
{
    int wstatus;
    int sig_res;
    sig_res = kill(forked_partitionId, SIGKILL);
    if (sig_res == -1) {
        perror("kill");
        exit(EXIT_FAILURE);
    }

    if (waitpid(forked_partitionId, &wstatus, WUNTRACED | WCONTINUED) == -1) {
        perror("waitpid");
        exit(EXIT_FAILURE);
    }
}

void SolverProcess::add_constraint(std::unique_ptr<PTPLib::net::map_solverBranch_lemmas> const & clauses, std::string & branch) {
    for ( const auto &lemmaPulled : *clauses ) {
        if (log_enabled)
            synced_stream.println(log_enabled ? PTPLib::common::Color::FG_Cyan : PTPLib::common::Color::FG_DEFAULT,
                                  "[ t ", __func__, "] -> "," check for Node -> "+ lemmaPulled.first);
        if (not lemmaPulled.first.empty()) {
            assert(not lemmaPulled.first.empty() and not branch.empty());
            if (isPrefix(lemmaPulled.first.substr(1, lemmaPulled.first.size() - 2),branch.substr(1, branch.size() - 2))) {
                if (log_enabled)
                    synced_stream.println_bold(log_enabled ? PTPLib::common::Color::FG_Cyan : PTPLib::common::Color::FG_DEFAULT,
                                               "[ t ", __func__, "] -> ", "Solver At: " , branch,
                                               " Injecting ", lemmaPulled.second.size(), " Clauses From: ", lemmaPulled.first);
                for (const auto & lemma : lemmaPulled.second)
                {
                    assert(lemma.clause.size());
                    if (log_enabled)
                        synced_stream.println(log_enabled ? PTPLib::common::Color::FG_Cyan : PTPLib::common::Color::FG_DEFAULT, lemma.clause);
                    std::string assertion = "(assert " + lemma.clause + ")";
                    splitterInterpret->interpFile((char *) assertion.c_str());
                    try {
                        z3State->solver.from_string(assertion.c_str());
                    }
                    catch (z3::exception & ex) {
                        PTPLib::net::Header header;
                        net::Report::error(get_SMTS_socket(), header, std::string("Z3 lemma injection error: ") + ex.msg());
                    }
                }
            }
        }
    }
}

void SolverProcess::getCnfClauses(PTPLib::net::SMTS_Event & smtsEvent) {
    if (smtsEvent.header.count(PTPLib::common::Param.QUERY)) {

        pid_t pid = getpid();
        if (fork() != 0) {
            return;
        }

        std::thread _t([&] {
            while (getppid() == pid) {
                sleep(1);
            }
            exit(0);
        });

        SMTConfig config;
        config.set_dryrun(true);
        if (not (splitterInterpret = new SplitterInterpret(config, getChannel())))
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

void SolverProcess::getCnfLearnts(PTPLib::net::Header &header) {
    std::string cnf = getMainSplitter().getSMTSolver().printCnfLearnts();
    net::Report::report(get_SMTS_socket(), header, header[PTPLib::common::Param.COMMAND], cnf);
}
