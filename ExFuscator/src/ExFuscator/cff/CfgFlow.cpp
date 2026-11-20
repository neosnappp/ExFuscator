#include "astra/cff/CfgFlow.hpp"

#include <algorithm>

namespace astra {
namespace cff {

int levelForSize(size_t bytes) {
    if (bytes < 4096) return 3;
    if (bytes < 16384) return 2;
    if (bytes < 65536) return 1;
    return 0;
}

CfgOptions optionsForLevel(int level) {
    CfgOptions o;
    switch (level) {
        case 0:
            o.flattenChance = 0.30;
            o.bogusChance = 0.0;
            o.junkChance = 0.0;
            o.minStats = 8;
            o.minNodes = 8;
            o.nodeBudget = 24;
            break;
        case 1:
            o.flattenChance = 0.55;
            o.bogusChance = 0.06;
            o.junkChance = 0.10;
            o.minStats = 5;
            o.minNodes = 6;
            o.nodeBudget = 36;
            break;
        case 2:
            o.flattenChance = 0.85;
            o.bogusChance = 0.15;
            o.junkChance = 0.25;
            o.minStats = 3;
            o.minNodes = 5;
            o.nodeBudget = 56;
            break;
        default:
            o.flattenChance = 1.00;
            o.bogusChance = 0.28;
            o.junkChance = 0.40;
            o.minStats = 2;
            o.minNodes = 4;
            o.nodeBudget = 96;
            break;
    }
    return o;
}

namespace {

using K = ast::Stmt::K;

struct Arena {
    std::vector<std::unique_ptr<ast::Expr>> exprs;
    std::vector<std::unique_ptr<ast::Stmt>> stmts;
    std::vector<std::unique_ptr<ast::Block>> blocks;
    std::vector<std::unique_ptr<ast::FuncLit>> funcs;

    ast::Expr* ex(ast::EK k, int line = 0) {
        auto e = std::make_unique<ast::Expr>(k);
        e->line = line;
        exprs.push_back(std::move(e));
        return exprs.back().get();
    }
    ast::Stmt* st(K k, int line = 0) {
        auto s = std::make_unique<ast::Stmt>(k);
        s->line = line;
        stmts.push_back(std::move(s));
        return stmts.back().get();
    }
    ast::Block* blk() {
        blocks.push_back(std::make_unique<ast::Block>());
        return blocks.back().get();
    }
    ast::Expr* num(std::int64_t v, int line = 0) {
        ast::Expr* e = ex(ast::EK::Num, line);
        e->num = (double)v;
        e->text = std::to_string(v);
        return e;
    }
    ast::Expr* nameRef(const std::string& n, int line = 0) {
        ast::Expr* e = ex(ast::EK::Name, line);
        e->text = n;
        return e;
    }
};

void allNamesExpr(ast::Expr* e, std::unordered_set<std::string>& out,
                  std::vector<ast::FuncLit*>& fns);
void allNamesBlock(ast::Block* b, std::unordered_set<std::string>& out,
                   std::vector<ast::FuncLit*>& fns);
void refsExpr(ast::Expr* e, std::unordered_set<std::string>& out);
void refsBlock(ast::Block* b, std::unordered_set<std::string>& out);
void capturedExpr(ast::Expr* e, std::unordered_set<std::string>& out);
void capturedBlock(ast::Block* b, std::unordered_set<std::string>& out);
bool nakedJumpBlock(ast::Block* b, int depth);

void allNamesExpr(ast::Expr* e, std::unordered_set<std::string>& out,
                  std::vector<ast::FuncLit*>& fns) {
    if (!e) return;
    switch (e->kind) {
        case ast::EK::Name:
            out.insert(e->text);
            break;
        case ast::EK::Func:
            if (e->fn) {
                fns.push_back(e->fn);
                for (const std::string& p : e->fn->params) out.insert(p);
                allNamesBlock(e->fn->body, out, fns);
            }
            break;
        case ast::EK::Bin:
            allNamesExpr(e->a, out, fns);
            allNamesExpr(e->b, out, fns);
            break;
        case ast::EK::Un:
            allNamesExpr(e->a, out, fns);
            break;
        case ast::EK::Call:
        case ast::EK::MCall:
            allNamesExpr(e->a, out, fns);
            for (ast::Expr* a : e->args) allNamesExpr(a, out, fns);
            break;
        case ast::EK::Index:
            allNamesExpr(e->a, out, fns);
            allNamesExpr(e->b, out, fns);
            break;
        case ast::EK::Table:
            for (ast::TableField& f : e->fields) {
                if (f.keyExpr) allNamesExpr(f.keyExpr, out, fns);
                allNamesExpr(f.value, out, fns);
            }
            break;
        default:
            break;
    }
}

void allNamesStmt(ast::Stmt* s, std::unordered_set<std::string>& out,
                  std::vector<ast::FuncLit*>& fns) {
    if (!s) return;
    switch (s->kind) {
        case K::Local:
            for (const std::string& n : s->names) out.insert(n);
            for (ast::Expr* e : s->exprs) allNamesExpr(e, out, fns);
            break;
        case K::LocalFunc:
            for (const std::string& n : s->names) out.insert(n);
            if (s->fn) {
                fns.push_back(s->fn);
                for (const std::string& p : s->fn->params) out.insert(p);
                allNamesBlock(s->fn->body, out, fns);
            }
            break;
        case K::Assign:
            for (ast::Expr* e : s->targets) allNamesExpr(e, out, fns);
            for (ast::Expr* e : s->exprs) allNamesExpr(e, out, fns);
            break;
        case K::Call:
            allNamesExpr(s->call, out, fns);
            break;
        case K::Do:
            allNamesBlock(s->body, out, fns);
            break;
        case K::While:
        case K::Repeat:
            for (ast::Expr* e : s->exprs) allNamesExpr(e, out, fns);
            allNamesBlock(s->body, out, fns);
            break;
        case K::If:
            for (ast::IfClause& c : s->clauses) {
                allNamesExpr(c.cond, out, fns);
                allNamesBlock(c.body, out, fns);
            }
            if (s->elseBody) allNamesBlock(s->elseBody, out, fns);
            break;
        case K::NumFor:
        case K::GenFor:
            for (ast::Expr* e : s->exprs) allNamesExpr(e, out, fns);
            allNamesBlock(s->body, out, fns);
            break;
        case K::Func:
            for (const std::string& p : s->path) out.insert(p);
            if (s->fn) {
                fns.push_back(s->fn);
                for (const std::string& p : s->fn->params) out.insert(p);
                allNamesBlock(s->fn->body, out, fns);
            }
            break;
        case K::Return:
            for (ast::Expr* e : s->exprs) allNamesExpr(e, out, fns);
            break;
        default:
            break;
    }
}

void allNamesBlock(ast::Block* b, std::unordered_set<std::string>& out,
                   std::vector<ast::FuncLit*>& fns) {
    if (!b) return;
    for (ast::Stmt* s : b->stats) allNamesStmt(s, out, fns);
}

void refsExpr(ast::Expr* e, std::unordered_set<std::string>& out) {
    if (!e) return;
    switch (e->kind) {
        case ast::EK::Name:
            out.insert(e->text);
            break;
        case ast::EK::Func:
            if (e->fn) {
                for (const std::string& p : e->fn->params) out.insert(p);
                refsBlock(e->fn->body, out);
            }
            break;
        case ast::EK::Bin:
            refsExpr(e->a, out);
            refsExpr(e->b, out);
            break;
        case ast::EK::Un:
            refsExpr(e->a, out);
            break;
        case ast::EK::Call:
        case ast::EK::MCall:
            refsExpr(e->a, out);
            for (ast::Expr* a : e->args) refsExpr(a, out);
            break;
        case ast::EK::Index:
            refsExpr(e->a, out);
            refsExpr(e->b, out);
            break;
        case ast::EK::Table:
            for (ast::TableField& f : e->fields) {
                if (f.keyExpr) refsExpr(f.keyExpr, out);
                refsExpr(f.value, out);
            }
            break;
        default:
            break;
    }
}

void refsStmt(ast::Stmt* s, std::unordered_set<std::string>& out) {
    if (!s) return;
    switch (s->kind) {
        case K::Local:
            for (ast::Expr* e : s->exprs) refsExpr(e, out);
            break;
        case K::LocalFunc:
            if (s->fn) {
                refsBlock(s->fn->body, out);
                out.erase(s->names[0]);
            }
            break;
        case K::Assign:
            for (ast::Expr* e : s->targets) refsExpr(e, out);
            for (ast::Expr* e : s->exprs) refsExpr(e, out);
            break;
        case K::Call:
            refsExpr(s->call, out);
            break;
        case K::Do:
            refsBlock(s->body, out);
            break;
        case K::While:
        case K::Repeat:
            for (ast::Expr* e : s->exprs) refsExpr(e, out);
            refsBlock(s->body, out);
            break;
        case K::If:
            for (ast::IfClause& c : s->clauses) {
                refsExpr(c.cond, out);
                refsBlock(c.body, out);
            }
            if (s->elseBody) refsBlock(s->elseBody, out);
            break;
        case K::NumFor:
        case K::GenFor:
            for (ast::Expr* e : s->exprs) refsExpr(e, out);
            refsBlock(s->body, out);
            break;
        case K::Func:
            for (const std::string& p : s->path) out.insert(p);
            if (s->fn) {
                refsBlock(s->fn->body, out);
            }
            break;
        case K::Return:
            for (ast::Expr* e : s->exprs) refsExpr(e, out);
            break;
        default:
            break;
    }
}

void refsBlock(ast::Block* b, std::unordered_set<std::string>& out) {
    if (!b) return;
    for (ast::Stmt* s : b->stats) refsStmt(s, out);
}

void capturedStmt(ast::Stmt* s, std::unordered_set<std::string>& out) {
    if (!s) return;
    switch (s->kind) {
        case K::Local:
            for (ast::Expr* e : s->exprs) {
                if (e && e->kind == ast::EK::Func && e->fn)
                    capturedBlock(e->fn->body, out);
            }
            break;
        case K::LocalFunc:
            if (s->fn) capturedBlock(s->fn->body, out);
            break;
        case K::Assign:
            for (ast::Expr* e : s->targets) capturedExpr(e, out);
            for (ast::Expr* e : s->exprs) capturedExpr(e, out);
            break;
        case K::Call:
            capturedExpr(s->call, out);
            break;
        case K::Do:
            capturedBlock(s->body, out);
            break;
        case K::While:
        case K::Repeat:
            for (ast::Expr* e : s->exprs) capturedExpr(e, out);
            capturedBlock(s->body, out);
            break;
        case K::If:
            for (ast::IfClause& c : s->clauses) {
                capturedExpr(c.cond, out);
                capturedBlock(c.body, out);
            }
            if (s->elseBody) capturedBlock(s->elseBody, out);
            break;
        case K::NumFor:
        case K::GenFor:
            for (ast::Expr* e : s->exprs) capturedExpr(e, out);
            capturedBlock(s->body, out);
            break;
        case K::Func:
            if (s->fn) capturedBlock(s->fn->body, out);
            break;
        case K::Return:
            for (ast::Expr* e : s->exprs) capturedExpr(e, out);
            break;
        default:
            break;
    }
}

void capturedExpr(ast::Expr* e, std::unordered_set<std::string>& out) {
    if (!e) return;
    if (e->kind == ast::EK::Func) {
        if (e->fn) capturedBlock(e->fn->body, out);
        return;
    }
    switch (e->kind) {
        case ast::EK::Bin:
            capturedExpr(e->a, out);
            capturedExpr(e->b, out);
            break;
        case ast::EK::Un:
            capturedExpr(e->a, out);
            break;
        case ast::EK::Call:
        case ast::EK::MCall:
            capturedExpr(e->a, out);
            for (ast::Expr* a : e->args) capturedExpr(a, out);
            break;
        case ast::EK::Index:
            capturedExpr(e->a, out);
            capturedExpr(e->b, out);
            break;
        case ast::EK::Table:
            for (ast::TableField& f : e->fields) {
                if (f.keyExpr) capturedExpr(f.keyExpr, out);
                capturedExpr(f.value, out);
            }
            break;
        default:
            break;
    }
}

void capturedBlock(ast::Block* b, std::unordered_set<std::string>& out) {
    if (!b) return;
    for (ast::Stmt* s : b->stats) capturedStmt(s, out);
}

bool nakedJumpStmt(ast::Stmt* s, int depth) {
    if (!s) return false;
    switch (s->kind) {
        case K::Break:
        case K::Continue:
            return depth == 0;
        case K::Do:
            return nakedJumpBlock(s->body, depth);
        case K::While:
        case K::Repeat:
        case K::NumFor:
        case K::GenFor:
            return nakedJumpBlock(s->body, depth + 1);
        case K::If:
            for (ast::IfClause& c : s->clauses)
                if (nakedJumpBlock(c.body, depth)) return true;
            if (s->elseBody && nakedJumpBlock(s->elseBody, depth)) return true;
            return false;
        default:
            return false;
    }
}

bool nakedJumpBlock(ast::Block* b, int depth) {
    if (!b) return false;
    for (ast::Stmt* s : b->stats)
        if (nakedJumpStmt(s, depth)) return true;
    return false;
}

struct RegionVerdict {
    bool ok = false;
    std::vector<std::string> hoist;
};

struct CNode {
    enum T { Linear, Branch, Loop, Terminal } t = Linear;
    std::vector<ast::Stmt*> stats;
    ast::Stmt* ctrl = nullptr;
    int id = 0;
    int fall = -1;
    int elseNode = -1;
    bool grouped = false;
    std::vector<int> branchTarget;
    int groupEnd = -1;
};

struct DeadState {
    int id = 0;
    ast::Block* body = nullptr;
};

class Cffer {
public:
    Cffer(std::uint64_t seed, const CfgOptions& opt, NameGen* shared)
        : rng_(seed), opt_(opt), shared_(shared) {
        static const char* kws[] = {
            "and", "break", "do", "else", "elseif", "end", "false",
            "for", "function", "goto", "if", "in", "local", "nil",
            "not", "or", "repeat", "return", "then", "true", "until",
            "while", "continue", "self"};
        for (const char* k : kws) gen_.reserve(k);
    }

    void run(ast::Chunk& chunk) {
        std::unordered_set<std::string> all;
        std::vector<ast::FuncLit*> fns;
        allNamesBlock(chunk.root, all, fns);
        gen_.reserveMany(all);
        processBlock(chunk.root, 0);
    }

    const CfgStats& stats() const { return stats_; }

private:
    Rng rng_;
    CfgOptions opt_;
    NameGen* shared_;
    NameGen gen_;
    Arena ar_;
    CfgStats stats_;
    std::unordered_set<ast::Block*> done_;

    void reserve(const std::string& n) {
        gen_.reserve(n);
        if (shared_) shared_->reserve(n);
    }

    void processBlock(ast::Block* b, int loopDepth, bool allowFlat = true) {
        if (!b) return;
        if (!done_.insert(b).second) return;
        bool flattened = false;
        if (allowFlat && loopDepth == 0 && opt_.flattenChance > 0.0 &&
            rng_.chance(opt_.flattenChance)) {
            RegionVerdict v = scanRegion(b, loopDepth);
            if (v.ok) {
                flattenRegion(b, v.hoist);
                flattened = true;
            }
        }
        if (flattened) {
            for (ast::Stmt* s : b->stats) {
                if (s->kind == K::Do) walkDispatcher(s, loopDepth);
                else walkStmt(s, loopDepth);
            }
        } else {
            for (ast::Stmt* s : b->stats) walkStmt(s, loopDepth);
        }
    }

    void walkDispatcher(ast::Stmt* dos, int loopDepth) {
        ast::Block* db = dos->body;
        if (!db || db->stats.size() < 2) return;
        ast::Stmt* wh = db->stats[1];
        if (wh->kind != K::While || !wh->body || wh->body->stats.empty()) return;
        ast::Stmt* ifs = wh->body->stats[0];
        if (ifs->kind != K::If) return;
        for (ast::IfClause& c : ifs->clauses) processBlock(c.body, loopDepth + 1, false);
    }

    void walkExprFns(ast::Expr* e, int loopDepth) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Func:
                if (e->fn) processBlock(e->fn->body, 0);
                break;
            case ast::EK::Bin:
                walkExprFns(e->a, loopDepth);
                walkExprFns(e->b, loopDepth);
                break;
            case ast::EK::Un:
                walkExprFns(e->a, loopDepth);
                break;
            case ast::EK::Call:
            case ast::EK::MCall:
                walkExprFns(e->a, loopDepth);
                for (ast::Expr* a : e->args) walkExprFns(a, loopDepth);
                break;
            case ast::EK::Index:
                walkExprFns(e->a, loopDepth);
                walkExprFns(e->b, loopDepth);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) walkExprFns(f.keyExpr, loopDepth);
                    walkExprFns(f.value, loopDepth);
                }
                break;
            default:
                break;
        }
    }

    void walkStmt(ast::Stmt* s, int loopDepth) {
        if (!s) return;
        switch (s->kind) {
            case K::Local:
            case K::Assign:
                for (ast::Expr* e : s->targets) walkExprFns(e, loopDepth);
                for (ast::Expr* e : s->exprs) walkExprFns(e, loopDepth);
                break;
            case K::LocalFunc:
            case K::Func:
                if (s->fn) processBlock(s->fn->body, 0);
                break;
            case K::Call:
                walkExprFns(s->call, loopDepth);
                break;
            case K::Do:
                processBlock(s->body, loopDepth);
                break;
            case K::While:
                for (ast::Expr* e : s->exprs) walkExprFns(e, loopDepth);
                processBlock(s->body, loopDepth + 1);
                break;
            case K::Repeat:
                processBlock(s->body, loopDepth + 1);
                for (ast::Expr* e : s->exprs) walkExprFns(e, loopDepth);
                break;
            case K::If:
                for (ast::IfClause& c : s->clauses) {
                    walkExprFns(c.cond, loopDepth);
                    processBlock(c.body, loopDepth);
                }
                if (s->elseBody) processBlock(s->elseBody, loopDepth);
                break;
            case K::NumFor:
            case K::GenFor:
                for (ast::Expr* e : s->exprs) walkExprFns(e, loopDepth);
                processBlock(s->body, loopDepth + 1);
                break;
            case K::Return:
                for (ast::Expr* e : s->exprs) walkExprFns(e, loopDepth);
                break;
            default:
                break;
        }
    }

    RegionVerdict scanRegion(ast::Block* b, int loopDepth) {
        RegionVerdict v;
        std::vector<ast::Stmt*> seq;
        for (ast::Stmt* s : b->stats)
            if (s->kind != K::Empty) seq.push_back(s);
        if ((int)seq.size() < (int)opt_.minStats) return v;
        if (nakedJumpBlock(b, 0)) return v;

        size_t est = 0;
        bool inLin = false;
        for (ast::Stmt* s : seq) {
            switch (s->kind) {
                case K::If:
                    if (inLin) {
                        ++est;
                        inLin = false;
                    }
                    est += 1 + s->clauses.size() + (s->elseBody ? 1 : 0);
                    break;
                case K::While:
                case K::Repeat:
                case K::NumFor:
                case K::GenFor:
                case K::Return:
                    if (inLin) {
                        ++est;
                        inLin = false;
                    }
                    ++est;
                    break;
                default:
                    inLin = true;
                    break;
            }
        }
        if (inLin) ++est;
        if (est < opt_.minNodes) return v;

        std::vector<std::string> decls;
        std::unordered_set<std::string> declSet;
        for (ast::Stmt* s : seq) {
            if (s->kind == K::Local || s->kind == K::LocalFunc) {
                for (const std::string& n : s->names) {
                    if (!declSet.insert(n).second) return v;
                    decls.push_back(n);
                }
            }
        }

        std::unordered_set<std::string> pending = declSet;
        for (ast::Stmt* s : seq) {
            std::unordered_set<std::string> refs;
            refsStmt(s, refs);
            for (const std::string& n : refs)
                if (pending.count(n)) return v;
            if (s->kind == K::Local) {
                for (const std::string& n : s->names) pending.erase(n);
            } else if (s->kind == K::LocalFunc) {
                pending.erase(s->names[0]);
            }
        }

        if (loopDepth > 0 && !declSet.empty()) {
            std::unordered_set<std::string> cap;
            capturedBlock(b, cap);
            for (const std::string& n : cap)
                if (declSet.count(n)) return v;
        }

        v.ok = true;
        v.hoist = std::move(decls);
        return v;
    }

    ast::Stmt* convertLocal(ast::Stmt* s) {
        if (s->exprs.empty()) return nullptr;
        ast::Stmt* a = ar_.st(K::Assign, s->line);
        for (const std::string& n : s->names)
            a->targets.push_back(ar_.nameRef(n, s->line));
        a->exprs = s->exprs;
        return a;
    }

    ast::Stmt* convertLocalFunc(ast::Stmt* s) {
        ast::Stmt* a = ar_.st(K::Assign, s->line);
        a->targets.push_back(ar_.nameRef(s->names[0], s->line));
        ast::Expr* fe = ar_.ex(ast::EK::Func, s->line);
        fe->fn = s->fn;
        a->exprs.push_back(fe);
        return a;
    }

    bool buildNodes(std::vector<ast::Stmt*>& stats, std::vector<CNode>& nodes) {
        nodes.clear();
        std::vector<ast::Stmt*> lin;
        auto flush = [&]() {
            if (!lin.empty()) {
                CNode n;
                n.t = CNode::Linear;
                n.stats = std::move(lin);
                nodes.push_back(std::move(n));
                lin.clear();
            }
        };
        for (size_t si = 0; si < stats.size(); ++si) {
            ast::Stmt* s = stats[si];
            if (s->kind == K::Empty) continue;
            switch (s->kind) {
                case K::Local:
                case K::LocalFunc: {
                    ast::Stmt* c =
                        s->kind == K::Local ? convertLocal(s) : convertLocalFunc(s);
                    if (c) lin.push_back(c);
                    break;
                }
                case K::If: {
                    flush();
                    int bi = (int)nodes.size();
                    CNode br;
                    br.t = CNode::Branch;
                    br.ctrl = s;
                    nodes.push_back(std::move(br));
                    for (ast::IfClause& c : s->clauses) {
                        CNode bn;
                        bn.t = CNode::Linear;
                        bn.stats = std::move(c.body->stats);
                        bn.grouped = true;
                        nodes.push_back(std::move(bn));
                        nodes[bi].branchTarget.push_back((int)nodes.size() - 1);
                    }
                    if (s->elseBody) {
                        CNode en;
                        en.t = CNode::Linear;
                        en.stats = std::move(s->elseBody->stats);
                        en.grouped = true;
                        nodes.push_back(std::move(en));
                        nodes[bi].elseNode = (int)nodes.size() - 1;
                    }
                    nodes[bi].groupEnd = (int)nodes.size() - 1;
                    break;
                }
                case K::While:
                case K::Repeat:
                case K::NumFor:
                case K::GenFor: {
                    flush();
                    CNode n;
                    n.t = CNode::Loop;
                    n.ctrl = s;
                    nodes.push_back(std::move(n));
                    break;
                }
                case K::Return: {
                    flush();
                    CNode n;
                    n.t = CNode::Terminal;
                    n.ctrl = s;
                    nodes.push_back(std::move(n));
                    finishNodes(nodes);
                    return true;
                }
                case K::Break:
                case K::Continue:
                    return false;
                default:
                    lin.push_back(s);
                    break;
            }
        }
        flush();
        if (nodes.empty()) return false;
        finishNodes(nodes);
        return true;
    }

    void finishNodes(std::vector<CNode>& nodes) {
        int n = (int)nodes.size();
        for (int i = 0; i < n; ++i) {
            CNode& nd = nodes[i];
            if (nd.t == CNode::Terminal) {
                nd.fall = -1;
            } else if (nd.t == CNode::Branch) {
                int after = nd.groupEnd + 1;
                int common = after < n ? after : -1;
                if (nd.elseNode >= 0) {
                    nodes[nd.elseNode].fall = common;
                    nd.fall = nd.elseNode;
                } else {
                    nd.fall = common;
                }
                for (int bt : nd.branchTarget) nodes[bt].fall = common;
            } else if (nd.t == CNode::Linear) {
                if (!nd.grouped) nd.fall = i + 1 < n ? i + 1 : -1;
            } else {
                nd.fall = i + 1 < n ? i + 1 : -1;
            }
        }
    }

    int freshId(std::unordered_set<int>& used) {
        for (;;) {
            int v = (int)rng_.irange(10000, 9999999);
            if (used.insert(v).second) return v;
        }
    }

    ast::Stmt* breakStmt() { return ar_.st(K::Break, 0); }

    ast::Stmt* setState(const std::string& var, int id) {
        ast::Stmt* a = ar_.st(K::Assign, 0);
        a->targets.push_back(ar_.nameRef(var, 0));
        a->exprs.push_back(ar_.num(id, 0));
        return a;
    }

    ast::Expr* opaquePred(const std::string& q, std::int64_t qv) {
        int form = (int)rng_.range(3);
        if (form == 0) {
            ast::Expr* e = ar_.ex(ast::EK::Bin);
            e->op = ast::SO::Lt;
            e->a = ar_.nameRef(q, 0);
            e->b = ar_.num(qv + 1 + rng_.irange(1, 1000), 0);
            return e;
        }
        if (form == 1) {
            ast::Expr* e = ar_.ex(ast::EK::Bin);
            e->op = ast::SO::Ne;
            e->a = ar_.nameRef(q, 0);
            std::int64_t d = qv + rng_.irange(1, 900000);
            if (rng_.chance(0.5)) d = qv - rng_.irange(1, 900000);
            if (d == qv) d = qv + 1;
            e->b = ar_.num(d, 0);
            return e;
        }
        std::int64_t p = rng_.irange(7, 997);
        std::int64_t c = rng_.irange(1, 100000);
        std::int64_t d = ((qv + c) % p + 1 + rng_.irange(0, p - 2)) % p;
        ast::Expr* m = ar_.ex(ast::EK::Bin);
        m->op = ast::SO::Mod;
        ast::Expr* pl = ar_.ex(ast::EK::Bin);
        pl->op = ast::SO::Add;
        pl->a = ar_.nameRef(q, 0);
        pl->b = ar_.num(c, 0);
        m->a = pl;
        m->b = ar_.num(p, 0);
        ast::Expr* e = ar_.ex(ast::EK::Bin);
        e->op = ast::SO::Ne;
        e->a = m;
        e->b = ar_.num(d, 0);
        return e;
    }

    ast::Block* junkBody(const std::vector<std::string>& jl) {
        ast::Block* body = ar_.blk();
        int nstat = 2 + (int)rng_.range(4);
        for (int i = 0; i < nstat; ++i) {
            const std::string& dst = jl[(size_t)rng_.range(jl.size())];
            const std::string& s1 = jl[(size_t)rng_.range(jl.size())];
            ast::Stmt* a = ar_.st(K::Assign, 0);
            a->targets.push_back(ar_.nameRef(dst, 0));
            ast::Expr* bin = ar_.ex(ast::EK::Bin);
            int sel = (int)rng_.range(4);
            if (sel == 0) bin->op = ast::SO::Add;
            else if (sel == 1) bin->op = ast::SO::Sub;
            else if (sel == 2) bin->op = ast::SO::Mul;
            else bin->op = ast::SO::Mod;
            bin->a = ar_.nameRef(s1, 0);
            if (jl.size() > 1 && rng_.chance(0.4)) {
                const std::string& s2 = jl[(size_t)rng_.range(jl.size())];
                bin->b = ar_.nameRef(s2, 0);
            } else {
                bin->b = ar_.num(rng_.irange(2, 999999), 0);
            }
            a->exprs.push_back(bin);
            body->stats.push_back(a);
        }
        body->stats.push_back(breakStmt());
        return body;
    }

    void transition(ast::Block* into, const std::string& var, int targetId,
                    const std::vector<DeadState>& deads,
                    const std::vector<std::pair<std::string, std::int64_t>>& qs) {
        if (targetId < 0) {
            into->stats.push_back(breakStmt());
            return;
        }
        if (!deads.empty() && !qs.empty() && rng_.chance(opt_.bogusChance)) {
            const DeadState& dd = deads[(size_t)rng_.range(deads.size())];
            const auto& qp = qs[(size_t)rng_.range(qs.size())];
            ast::Stmt* ifs = ar_.st(K::If, 0);
            ast::IfClause c;
            c.cond = opaquePred(qp.first, qp.second);
            ast::Block* tb = ar_.blk();
            tb->stats.push_back(setState(var, targetId));
            c.body = tb;
            ifs->clauses.push_back(std::move(c));
            ast::Block* eb = ar_.blk();
            eb->stats.push_back(setState(var, dd.id));
            ifs->elseBody = eb;
            into->stats.push_back(ifs);
            ++stats_.bogus;
            return;
        }
        into->stats.push_back(setState(var, targetId));
    }

    ast::Stmt* emitChunk(std::vector<CNode>& nodes, int s, int e,
                         std::unordered_set<int>& used,
                         const std::vector<std::string>& jl,
                         const std::vector<std::pair<std::string, std::int64_t>>& qs) {
        std::vector<DeadState> deads;
        int ndead = jl.empty()
                        ? 0
                        : (int)((double)(e - s) * opt_.junkChance *
                                (0.5 + (double)rng_.range(15) / 10.0));
        if (ndead > (e - s) / 2 + 1) ndead = (e - s) / 2 + 1;
        for (int i = 0; i < ndead; ++i) {
            DeadState d;
            d.id = freshId(used);
            d.body = junkBody(jl);
            deads.push_back(std::move(d));
            ++stats_.dead;
        }

        for (int i = s; i < e; ++i) nodes[i].id = freshId(used);
        std::string var = gen_.next();
        reserve(var);

        std::vector<int> order;
        for (int i = s; i < e; ++i) order.push_back(i);
        for (size_t k = order.size(); k > 1; --k) {
            size_t j = (size_t)rng_.range(k);
            std::swap(order[k - 1], order[j]);
        }

        auto tidOf = [&](int idx) -> int {
            return idx >= s && idx < e ? nodes[idx].id : -1;
        };

        std::vector<ast::IfClause> clauses;
        for (int i : order) {
            CNode& nd = nodes[i];
            ast::IfClause c;
            c.cond = ar_.ex(ast::EK::Bin);
            c.cond->op = ast::SO::Eq;
            c.cond->a = ar_.nameRef(var, 0);
            c.cond->b = ar_.num(nd.id, 0);
            ast::Block* body = ar_.blk();
            switch (nd.t) {
                case CNode::Linear:
                    for (ast::Stmt* st : nd.stats) body->stats.push_back(st);
                    transition(body, var, tidOf(nd.fall), deads, qs);
                    break;
                case CNode::Loop:
                    body->stats.push_back(nd.ctrl);
                    transition(body, var, tidOf(nd.fall), deads, qs);
                    break;
                case CNode::Terminal:
                    body->stats.push_back(nd.ctrl);
                    break;
                case CNode::Branch: {
                    ast::Stmt* ifs = ar_.st(K::If, nd.ctrl->line);
                    for (size_t ci = 0; ci < nd.ctrl->clauses.size(); ++ci) {
                        ast::IfClause oc;
                        oc.cond = nd.ctrl->clauses[ci].cond;
                        ast::Block* tb = ar_.blk();
                        tb->stats.push_back(setState(var, nodes[nd.branchTarget[ci]].id));
                        oc.body = tb;
                        ifs->clauses.push_back(std::move(oc));
                    }
                    ast::Block* eb = ar_.blk();
                    if (tidOf(nd.fall) >= 0) {
                        eb->stats.push_back(setState(var, tidOf(nd.fall)));
                    } else {
                        eb->stats.push_back(breakStmt());
                    }
                    ifs->elseBody = eb;
                    body->stats.push_back(ifs);
                    break;
                }
            }
            c.body = body;
            clauses.push_back(std::move(c));
        }

        ast::Stmt* ifs = ar_.st(K::If, 0);
        ifs->clauses = std::move(clauses);
        ast::Block* els = ar_.blk();
        els->stats.push_back(breakStmt());
        ifs->elseBody = els;

        ast::Stmt* wh = ar_.st(K::While, 0);
        wh->exprs.push_back(ar_.ex(ast::EK::True));
        wh->body = ar_.blk();
        wh->body->stats.push_back(ifs);

        ast::Stmt* init = ar_.st(K::Local, 0);
        init->names.push_back(var);
        init->exprs.push_back(ar_.num(nodes[s].id, 0));

        ast::Stmt* dos = ar_.st(K::Do, 0);
        dos->body = ar_.blk();
        dos->body->stats.push_back(init);
        dos->body->stats.push_back(wh);

        stats_.states += (e - s);
        return dos;
    }

    void flattenRegion(ast::Block* b, const std::vector<std::string>& hoist) {
        std::vector<CNode> nodes;
        if (!buildNodes(b->stats, nodes)) return;

        std::vector<std::string> jl;
        bool wantJunk = opt_.junkChance > 0.0 && nodes.size() >= 6;
        if (wantJunk) {
            int nj = 1 + (int)rng_.range(3);
            for (int i = 0; i < nj; ++i) {
                std::string j = gen_.next();
                reserve(j);
                jl.push_back(j);
            }
        }

        std::vector<std::pair<std::string, std::int64_t>> qs;
        if (opt_.bogusChance > 0.0 && nodes.size() >= 6) {
            int nq = 1 + (int)rng_.range(2);
            for (int i = 0; i < nq; ++i) {
                std::string q = gen_.next();
                reserve(q);
                qs.push_back({q, rng_.irange(1000000, 2000000000)});
            }
        }

        std::unordered_set<int> used;
        std::vector<ast::Stmt*> out;
        if (!hoist.empty()) {
            ast::Stmt* h = ar_.st(K::Local, 0);
            h->names = hoist;
            out.push_back(h);
        }
        if (nodes.empty()) {
            b->stats = std::move(out);
            return;
        }
        if (!qs.empty() || !jl.empty()) {
            ast::Stmt* qd = ar_.st(K::Local, 0);
            for (const auto& qp : qs) {
                qd->names.push_back(qp.first);
                qd->exprs.push_back(ar_.num(qp.second, 0));
            }
            for (const std::string& j : jl) qd->names.push_back(j);
            out.push_back(qd);
        }

        int n = (int)nodes.size();
        int start = 0;
        int count = 0;
        int lastGroupEnd = -1;
        auto flushChunk = [&](int s, int e) {
            if (s >= e) return;
            if (e - s == 1 && nodes[s].t != CNode::Branch) {
                if (nodes[s].t == CNode::Loop || nodes[s].t == CNode::Terminal) {
                    out.push_back(nodes[s].ctrl);
                } else {
                    for (ast::Stmt* st : nodes[s].stats) out.push_back(st);
                }
                return;
            }
            out.push_back(emitChunk(nodes, s, e, used, jl, qs));
        };
        for (int i = 0; i < n; ++i) {
            if (nodes[i].t == CNode::Loop) {
                flushChunk(start, i);
                flushChunk(i, i + 1);
                start = i + 1;
                count = 0;
                lastGroupEnd = -1;
                continue;
            }
            if (nodes[i].t == CNode::Branch) lastGroupEnd = nodes[i].groupEnd;
            ++count;
            bool canCut = i >= lastGroupEnd;
            if (count >= (int)opt_.nodeBudget && canCut && i + 1 < n) {
                flushChunk(start, i + 1);
                start = i + 1;
                count = 0;
                lastGroupEnd = -1;
            }
        }
        flushChunk(start, n);

        b->stats = std::move(out);
        ++stats_.regions;
    }
};

}

CfgStats runCfgFlow(ast::Chunk& chunk, std::uint64_t seed, const CfgOptions& opt,
                    NameGen* sharedNames) {
    Cffer* c = new Cffer(seed, opt, sharedNames);
    c->run(chunk);
    return c->stats();
}

}
}
