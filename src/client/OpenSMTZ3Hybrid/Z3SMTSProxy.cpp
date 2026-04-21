#include "z3++.h"

#include <cctype>
#include <csignal>
#include <iostream>
#include <string>

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

static bool readTopLevelCommand(std::istream & in, std::string & out) {
    out.clear();
    int depth = 0;
    bool inString = false;
    bool inQuotedSymbol = false;
    bool inComment = false;
    bool started = false;

    char c;
    while (in.get(c)) {
        if (!started) {
            if (std::isspace(static_cast<unsigned char>(c))) continue;
            if (c == ';') {
                while (in.get(c) && c != '\n') {}
                continue;
            }
            if (c != '(') continue;
            started = true;
            depth = 1;
            out.push_back(c);
            continue;
        }

        out.push_back(c);
        if (inComment) {
            if (c == '\n') inComment = false;
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
        if (inString || inQuotedSymbol) continue;
        if (c == '(') ++depth;
        else if (c == ')') {
            --depth;
            if (depth == 0) return true;
        }
    }
    return false;
}

static std::string serializeClause(z3::expr_vector const & clause) {
    if (clause.size() == 1) return clause[0].to_string();
    std::string out = "(or";
    for (unsigned i = 0; i < clause.size(); ++i) {
        out += " ";
        out += clause[i].to_string();
    }
    out += ")";
    return out;
}

int main() {
    signal(SIGPIPE, SIG_IGN);

    z3::context context;
    z3::solver solver(context);
    bool collecting = false;

    z3::on_clause_eh_t onClause = [&](z3::expr const & proof,
                                      std::vector<unsigned> const &,
                                      z3::expr_vector const & clause) {
        if (!collecting) return;
        if (clause.empty() || clause.size() > 3) return;

        std::string proofText = proof.to_string();
        if (proofText.find("del") != std::string::npos ||
            proofText.find("asserted") != std::string::npos) {
            return;
        }

        std::cout << "smts-lemma " << serializeClause(clause) << "\n";
        std::cout.flush();
    };
    z3::on_clause clauseHook(solver, onClause);

    std::string command;
    while (readTopLevelCommand(std::cin, command)) {
        try {
            if (isCommand(command, "push")) {
                unsigned n = commandArgumentOrOne(command);
                for (unsigned i = 0; i < n; ++i) solver.push();
            }
            else if (isCommand(command, "pop")) {
                solver.pop(commandArgumentOrOne(command));
            }
            else if (isCommand(command, "check-sat")) {
                collecting = true;
                z3::check_result result = solver.check();
                collecting = false;
                if (result == z3::sat) std::cout << "sat\n";
                else if (result == z3::unsat) std::cout << "unsat\n";
                else std::cout << "unknown\n";
                std::cout.flush();
            }
            else if (isCommand(command, "exit")) {
                break;
            }
            else if (isCommand(command, "get-model") ||
                     isCommand(command, "get-value") ||
                     isCommand(command, "get-info") ||
                     isCommand(command, "get-unsat-core")) {
                continue;
            }
            else {
                solver.from_string(command.c_str());
            }
        }
        catch (z3::exception const & ex) {
            collecting = false;
            std::cout << "smts-error " << ex.msg() << "\n";
            std::cout.flush();
        }
        catch (std::exception const & ex) {
            collecting = false;
            std::cout << "smts-error " << ex.what() << "\n";
            std::cout.flush();
        }
    }

    return 0;
}
