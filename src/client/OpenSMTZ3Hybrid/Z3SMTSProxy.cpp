#include "z3++.h"

#include <algorithm>
#include <cctype>
#include <csignal>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Branch = std::vector<std::pair<int, int>>;

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

static bool smtsDepthCommand(std::string const & command, int & depth) {
    std::string const marker = ":smts-depth";
    size_t pos = command.find(marker);
    if (!isCommand(command, "set-info") || pos == std::string::npos) return false;
    pos += marker.size();
    while (pos < command.size() && std::isspace(static_cast<unsigned char>(command[pos]))) ++pos;
    size_t end = pos;
    while (end < command.size() && std::isdigit(static_cast<unsigned char>(command[end]))) ++end;
    if (end == pos) return true;
    depth = std::stoi(command.substr(pos, end - pos));
    return true;
}

static bool smtsBranchCommand(std::string const & command, Branch & branch) {
    if (!isCommand(command, "smts-branch")) return false;
    size_t i = command.find("smts-branch");
    if (i == std::string::npos) return true;
    i += std::string("smts-branch").size();

    Branch parsed;
    while (i < command.size()) {
        while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i]))) ++i;
        if (i == command.size() || command[i] == ')') break;

        size_t colon = command.find(':', i);
        if (colon == std::string::npos) break;
        size_t end = colon + 1;
        while (end < command.size() &&
               (std::isdigit(static_cast<unsigned char>(command[end])) || command[end] == '-')) {
            ++end;
        }
        parsed.emplace_back(std::stoi(command.substr(i, colon - i)),
                            std::stoi(command.substr(colon + 1, end - colon - 1)));
        i = end;
    }
    branch = std::move(parsed);
    return true;
}

static bool isPrefix(Branch const & prefix, Branch const & full) {
    if (prefix.size() > full.size()) return false;
    for (size_t i = 0; i < prefix.size(); ++i) {
        if (prefix[i] != full[i]) return false;
    }
    return true;
}

static std::string frameName(int id) {
    return ".frame" + std::to_string(id);
}

static z3::expr frameExpr(z3::context & context, int id) {
    return context.bool_const(frameName(id).c_str());
}

static bool extractAssertBody(std::string const & command, std::string & body) {
    if (!isCommand(command, "assert")) return false;
    size_t i = command.find("assert");
    if (i == std::string::npos) return false;
    i += std::string("assert").size();
    while (i < command.size() && std::isspace(static_cast<unsigned char>(command[i]))) ++i;
    size_t end = command.find_last_not_of(" \t\r\n");
    if (end == std::string::npos || command[end] != ')' || i >= end) return false;
    body = command.substr(i, end - i);
    return true;
}

static bool frameLiteral(z3::expr const & literal, int & id) {
    z3::expr atom = literal;
    if (literal.is_not() && literal.num_args() == 1) atom = literal.arg(0);
    if (!atom.is_const()) return false;
    std::string name = atom.decl().name().str();
    std::string const prefix = ".frame";
    if (name.compare(0, prefix.size(), prefix) != 0) return false;
    if (name.size() == prefix.size()) return false;
    for (size_t i = prefix.size(); i < name.size(); ++i) {
        if (!std::isdigit(static_cast<unsigned char>(name[i]))) return false;
    }
    id = std::stoi(name.substr(prefix.size()));
    return true;
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
    std::unordered_set<std::string> published;
    Branch targetBranch;
    std::unordered_map<int, Branch> frameBranches;
    std::vector<int> activeFrames{0};
    int nextFrameId = 1;

    // Fallback only.  Normal lemma levels are computed exactly from frame
    // literals, matching OpenSMT's ScatterSplitter::exposeLongerClauses.
    int currentDepth = 0;

    z3::on_clause_eh_t onClause = [&](z3::expr const & proof,
                                      std::vector<unsigned> const &,
                                      z3::expr_vector const & clause) {
        if (!collecting) return;
        if (clause.empty()) return;

        bool isDelete = false;

        // Check only the top-level proof rule, not the whole proof tree.
        // Searching proof.to_string() is fragile: a valid derived lemma whose
        // proof sub-tree mentions "asserted" would be wrongly suppressed.
        if (proof.is_app()) {
            std::string kind = proof.decl().name().str();
            if (kind == "asserted") return;
            isDelete = kind == "del";
        }

        int level = 0;
        bool hasForeignFrame = false;
        z3::expr_vector stripped(context);
        for (unsigned i = 0; i < clause.size(); ++i) {
            int frameId = 0;
            if (frameLiteral(clause[i], frameId)) {
                auto it = frameBranches.find(frameId);
                if (it == frameBranches.end() || !isPrefix(it->second, targetBranch)) {
                    hasForeignFrame = true;
                    break;
                }
                level = std::max<int>(level, static_cast<int>(it->second.size()));
                continue;
            }
            stripped.push_back(clause[i]);
        }

        if (hasForeignFrame || stripped.empty() || stripped.size() > 3) return;

        std::string clauseText = serializeClause(stripped);
        std::string key = std::to_string(level) + "\n" + clauseText;
        if (isDelete) {
            published.erase(key);
            std::cout << "smts-delete " << level << " " << clauseText << "\n";
            std::cout.flush();
            return;
        }
        if (!published.insert(key).second) return;

        std::cout << "smts-lemma " << level << " " << clauseText << "\n";
        std::cout.flush();
    };
    z3::on_clause clauseHook(solver, onClause);

    std::string command;
    while (readTopLevelCommand(std::cin, command)) {
        try {
            if (isCommand(command, "push")) {
                unsigned n = commandArgumentOrOne(command);
                for (unsigned i = 0; i < n; ++i) {
                    int frameId = nextFrameId++;
                    size_t depth = activeFrames.size();
                    Branch branchPrefix(targetBranch.begin(),
                        targetBranch.begin() + std::min(depth, targetBranch.size()));
                    frameBranches.emplace(frameId, std::move(branchPrefix));
                    solver.from_string(("(declare-const " + frameName(frameId) + " Bool)").c_str());
                    activeFrames.push_back(frameId);
                }
                currentDepth = static_cast<int>(activeFrames.size() - 1);
            }
            else if (isCommand(command, "pop")) {
                unsigned n = commandArgumentOrOne(command);
                while (n-- > 0 && activeFrames.size() > 1) activeFrames.pop_back();
                currentDepth = static_cast<int>(activeFrames.size() - 1);
            }
            else if (isCommand(command, "check-sat")) {
                z3::expr_vector assumptions(context);
                for (auto const & [frameId, branch] : frameBranches) {
                    z3::expr frame = frameExpr(context, frameId);
                    if (isPrefix(branch, targetBranch)) assumptions.push_back(!frame);
                    else assumptions.push_back(frame);
                }
                collecting = true;
                z3::check_result result = solver.check(assumptions);
                collecting = false;
                if (result == z3::sat) std::cout << "sat\n";
                else if (result == z3::unsat) std::cout << "unsat\n";
                else std::cout << "unknown\n";
                std::cout.flush();
            }
            else if (isCommand(command, "exit")) {
                break;
            }
            else if (smtsDepthCommand(command, currentDepth)) {
                continue;
            }
            else if (smtsBranchCommand(command, targetBranch)) {
                currentDepth = static_cast<int>(targetBranch.size());
                continue;
            }
            else if (isCommand(command, "get-model") ||
                     isCommand(command, "get-value") ||
                     isCommand(command, "get-info") ||
                     isCommand(command, "get-unsat-core")) {
                continue;
            }
            else {
                std::string assertionBody;
                if (extractAssertBody(command, assertionBody) && activeFrames.back() != 0) {
                    std::string guarded = "(assert (or " + frameName(activeFrames.back()) + " " + assertionBody + "))";
                    solver.from_string(guarded.c_str());
                } else {
                    solver.from_string(command.c_str());
                }
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
