#include "astra/passes/Pass.hpp"

namespace astra {
namespace passes {

namespace {

using K = ast::Stmt::K;

class ProxyPass {
public:
    ProxyPass(PassContext& ctx, double fnChance, int cap)
        : ctx_(ctx), fnChance_(fnChance), cap_(cap) {}

    void run(ast::Chunk& chunk) {
        collectDeclared(chunk.root);
        collectOwnedGlobals(chunk.root);
        std::vector<ast::Block*> fns{chunk.root};
        collectFnBodies(chunk.root, fns);
        for (ast::Block* b : fns)
            if (b) processFn(b);
    }

    int proxies() const { return proxies_; }

private:
    PassContext& ctx_;
    double fnChance_;
    int cap_;
    int proxies_ = 0;
    std::unordered_set<std::string> declared_;
    std::unordered_set<std::string> owned_;

    void collectOwnedGlobals(ast::Block* b) {
        for (ast::Stmt* s : b->stats) {
            switch (s->kind) {
                case K::Assign:
                    for (ast::Expr* t : s->targets)
                        if (t->kind == ast::EK::Name) owned_.insert(t->text);
                    for (ast::Expr* e : s->exprs) ownedExpr(e);
                    break;
                case K::Local:
                    for (ast::Expr* e : s->exprs) ownedExpr(e);
                    break;
                case K::LocalFunc:
                    collectOwnedGlobals(s->fn->body);
                    break;
                case K::Call:
                    ownedExpr(s->call);
                    break;
                case K::Do:
                    collectOwnedGlobals(s->body);
                    break;
                case K::While:
                    ownedExpr(s->exprs[0]);
                    collectOwnedGlobals(s->body);
                    break;
                case K::Repeat:
                    collectOwnedGlobals(s->body);
                    ownedExpr(s->exprs[0]);
                    break;
                case K::If:
                    for (ast::IfClause& c : s->clauses) {
                        ownedExpr(c.cond);
                        collectOwnedGlobals(c.body);
                    }
                    if (s->elseBody) collectOwnedGlobals(s->elseBody);
                    break;
                case K::NumFor:
                case K::GenFor:
                    for (ast::Expr* e : s->exprs) ownedExpr(e);
                    collectOwnedGlobals(s->body);
                    break;
                case K::Func:
                    owned_.insert(s->path[0]);
                    collectOwnedGlobals(s->fn->body);
                    break;
                case K::Return:
                    for (ast::Expr* e : s->exprs) ownedExpr(e);
                    break;
                default:
                    break;
            }
        }
    }

    void ownedExpr(ast::Expr* e) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Func:
                collectOwnedGlobals(e->fn->body);
                break;
            case ast::EK::Bin:
                ownedExpr(e->a); ownedExpr(e->b);
                break;
            case ast::EK::Un:
                ownedExpr(e->a);
                break;
            case ast::EK::Call: case ast::EK::MCall:
                ownedExpr(e->a);
                for (ast::Expr* a : e->args) ownedExpr(a);
                break;
            case ast::EK::Index:
                ownedExpr(e->a); ownedExpr(e->b);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) ownedExpr(f.keyExpr);
                    ownedExpr(f.value);
                }
                break;
            default:
                break;
        }
    }

    void collectDeclared(ast::Block* b) {
        for (ast::Stmt* s : b->stats) {
            switch (s->kind) {
                case K::Local:
                    for (const std::string& n : s->names) declared_.insert(n);
                    for (ast::Expr* e : s->exprs) collectDeclaredExpr(e);
                    break;
                case K::LocalFunc:
                    declared_.insert(s->names[0]);
                    collectDeclared(s->fn->body);
                    for (const std::string& p : s->fn->params) declared_.insert(p);
                    break;
                case K::Assign:
                    for (ast::Expr* e : s->targets) collectDeclaredExpr(e);
                    for (ast::Expr* e : s->exprs) collectDeclaredExpr(e);
                    break;
                case K::Call:
                    collectDeclaredExpr(s->call);
                    break;
                case K::Do:
                    collectDeclared(s->body);
                    break;
                case K::While:
                    collectDeclaredExpr(s->exprs[0]);
                    collectDeclared(s->body);
                    break;
                case K::Repeat:
                    collectDeclared(s->body);
                    collectDeclaredExpr(s->exprs[0]);
                    break;
                case K::If:
                    for (ast::IfClause& c : s->clauses) {
                        collectDeclaredExpr(c.cond);
                        collectDeclared(c.body);
                    }
                    if (s->elseBody) collectDeclared(s->elseBody);
                    break;
                case K::NumFor:
                    declared_.insert(s->names[0]);
                    for (ast::Expr* e : s->exprs) collectDeclaredExpr(e);
                    collectDeclared(s->body);
                    break;
                case K::GenFor:
                    for (const std::string& n : s->names) declared_.insert(n);
                    for (ast::Expr* e : s->exprs) collectDeclaredExpr(e);
                    collectDeclared(s->body);
                    break;
                case K::Func:
                    for (const std::string& p : s->fn->params) declared_.insert(p);
                    collectDeclared(s->fn->body);
                    break;
                case K::Return:
                    for (ast::Expr* e : s->exprs) collectDeclaredExpr(e);
                    break;
                default:
                    break;
            }
        }
    }

    void collectDeclaredExpr(ast::Expr* e) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Func:
                for (const std::string& p : e->fn->params) declared_.insert(p);
                collectDeclared(e->fn->body);
                break;
            case ast::EK::Bin:
                collectDeclaredExpr(e->a); collectDeclaredExpr(e->b);
                break;
            case ast::EK::Un:
                collectDeclaredExpr(e->a);
                break;
            case ast::EK::Call: case ast::EK::MCall:
                collectDeclaredExpr(e->a);
                for (ast::Expr* a : e->args) collectDeclaredExpr(a);
                break;
            case ast::EK::Index:
                collectDeclaredExpr(e->a); collectDeclaredExpr(e->b);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) collectDeclaredExpr(f.keyExpr);
                    collectDeclaredExpr(f.value);
                }
                break;
            default:
                break;
        }
    }

    void collectFnBodies(ast::Block* b, std::vector<ast::Block*>& out) {
        for (ast::Stmt* s : b->stats) {
            switch (s->kind) {
                case K::LocalFunc:
                    out.push_back(s->fn->body);
                    collectFnBodies(s->fn->body, out);
                    break;
                case K::Func:
                    out.push_back(s->fn->body);
                    collectFnBodies(s->fn->body, out);
                    break;
                case K::Do:
                    collectFnBodies(s->body, out);
                    break;
                case K::While:
                    collectFnExpr(s->exprs[0], out);
                    collectFnBodies(s->body, out);
                    break;
                case K::Repeat:
                    collectFnBodies(s->body, out);
                    collectFnExpr(s->exprs[0], out);
                    break;
                case K::If:
                    for (ast::IfClause& c : s->clauses) {
                        collectFnExpr(c.cond, out);
                        collectFnBodies(c.body, out);
                    }
                    if (s->elseBody) collectFnBodies(s->elseBody, out);
                    break;
                case K::NumFor:
                case K::GenFor:
                    for (ast::Expr* e : s->exprs) collectFnExpr(e, out);
                    collectFnBodies(s->body, out);
                    break;
                default:
                    for (ast::Expr* e : s->exprs) collectFnExpr(e, out);
                    for (ast::Expr* e : s->targets) collectFnExpr(e, out);
                    if (s->call) collectFnExpr(s->call, out);
                    break;
            }
        }
    }

    void collectFnExpr(ast::Expr* e, std::vector<ast::Block*>& out) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Func:
                out.push_back(e->fn->body);
                collectFnBodies(e->fn->body, out);
                break;
            case ast::EK::Bin:
                collectFnExpr(e->a, out); collectFnExpr(e->b, out);
                break;
            case ast::EK::Un:
                collectFnExpr(e->a, out);
                break;
            case ast::EK::Call: case ast::EK::MCall:
                collectFnExpr(e->a, out);
                for (ast::Expr* a : e->args) collectFnExpr(a, out);
                break;
            case ast::EK::Index:
                collectFnExpr(e->a, out); collectFnExpr(e->b, out);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) collectFnExpr(f.keyExpr, out);
                    collectFnExpr(f.value, out);
                }
                break;
            default:
                break;
        }
    }

    void processFn(ast::Block* body) {
        if (!ctx_.rng.chance(fnChance_)) return;

        std::unordered_map<std::string, int> count;
        scanCalls(body, count);
        if (count.empty()) return;

        std::vector<std::string> names;
        for (const auto& kv : count) names.push_back(kv.first);
        for (size_t k = names.size(); k > 1; --k) {
            size_t j = (size_t)ctx_.rng.range(k);
            std::swap(names[k - 1], names[j]);
        }
        if ((int)names.size() > cap_) names.resize((size_t)cap_);

        std::unordered_map<std::string, std::string> map;
        std::vector<ast::Stmt*> pre;
        for (const std::string& g : names) {
            std::string p = ctx_.gen.next();
            declared_.insert(p);
            ast::Stmt* d = ctx_.st(K::Local);
            d->names.push_back(p);
            ast::Expr* ref = ctx_.ex(ast::EK::Name);
            ref->text = g;
            d->exprs.push_back(ref);
            pre.push_back(d);
            map[g] = p;
        }
        body->stats.insert(body->stats.begin(), pre.begin(), pre.end());
        proxies_ += (int)map.size();

        replaceCalls(body, map);
    }

    void scanCalls(ast::Block* b, std::unordered_map<std::string, int>& count) {
        for (ast::Stmt* s : b->stats) {
            switch (s->kind) {
                case K::Local:
                    for (ast::Expr* e : s->exprs) scanCallsExpr(e, count);
                    break;
                case K::LocalFunc:
                    scanCalls(s->fn->body, count);
                    break;
                case K::Assign:
                    for (ast::Expr* e : s->targets) scanCallsExpr(e, count);
                    for (ast::Expr* e : s->exprs) scanCallsExpr(e, count);
                    break;
                case K::Call:
                    scanCallsExpr(s->call, count);
                    break;
                case K::Do:
                    scanCalls(s->body, count);
                    break;
                case K::While:
                    scanCallsExpr(s->exprs[0], count);
                    scanCalls(s->body, count);
                    break;
                case K::Repeat:
                    scanCalls(s->body, count);
                    scanCallsExpr(s->exprs[0], count);
                    break;
                case K::If:
                    for (ast::IfClause& c : s->clauses) {
                        scanCallsExpr(c.cond, count);
                        scanCalls(c.body, count);
                    }
                    if (s->elseBody) scanCalls(s->elseBody, count);
                    break;
                case K::NumFor:
                case K::GenFor:
                    for (ast::Expr* e : s->exprs) scanCallsExpr(e, count);
                    scanCalls(s->body, count);
                    break;
                case K::Func:
                    scanCalls(s->fn->body, count);
                    break;
                case K::Return:
                    for (ast::Expr* e : s->exprs) scanCallsExpr(e, count);
                    break;
                default:
                    break;
            }
        }
    }

    void scanCallsExpr(ast::Expr* e, std::unordered_map<std::string, int>& count) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Call:

                if (e->a && e->a->kind == ast::EK::Name &&
                    !declared_.count(e->a->text) && !owned_.count(e->a->text))
                    ++count[e->a->text];
                scanCallsExpr(e->a, count);
                for (ast::Expr* a : e->args) scanCallsExpr(a, count);
                break;
            case ast::EK::MCall:
                scanCallsExpr(e->a, count);
                for (ast::Expr* a : e->args) scanCallsExpr(a, count);
                break;
            case ast::EK::Func:
                scanCalls(e->fn->body, count);
                break;
            case ast::EK::Bin:
                scanCallsExpr(e->a, count); scanCallsExpr(e->b, count);
                break;
            case ast::EK::Un:
                scanCallsExpr(e->a, count);
                break;
            case ast::EK::Index:
                scanCallsExpr(e->a, count); scanCallsExpr(e->b, count);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) scanCallsExpr(f.keyExpr, count);
                    scanCallsExpr(f.value, count);
                }
                break;
            default:
                break;
        }
    }

    void replaceCalls(ast::Block* b,
                      const std::unordered_map<std::string, std::string>& map) {
        for (ast::Stmt* s : b->stats) {
            switch (s->kind) {
                case K::Local:
                    for (ast::Expr* e : s->exprs) replaceExpr(e, map);
                    break;
                case K::LocalFunc:
                    replaceCalls(s->fn->body, map);
                    break;
                case K::Assign:
                    for (ast::Expr* e : s->targets) replaceExpr(e, map);
                    for (ast::Expr* e : s->exprs) replaceExpr(e, map);
                    break;
                case K::Call:
                    replaceExpr(s->call, map);
                    break;
                case K::Do:
                    replaceCalls(s->body, map);
                    break;
                case K::While:
                    replaceExpr(s->exprs[0], map);
                    replaceCalls(s->body, map);
                    break;
                case K::Repeat:
                    replaceCalls(s->body, map);
                    replaceExpr(s->exprs[0], map);
                    break;
                case K::If:
                    for (ast::IfClause& c : s->clauses) {
                        replaceExpr(c.cond, map);
                        replaceCalls(c.body, map);
                    }
                    if (s->elseBody) replaceCalls(s->elseBody, map);
                    break;
                case K::NumFor:
                case K::GenFor:
                    for (ast::Expr* e : s->exprs) replaceExpr(e, map);
                    replaceCalls(s->body, map);
                    break;
                case K::Func:
                    replaceCalls(s->fn->body, map);
                    break;
                case K::Return:
                    for (ast::Expr* e : s->exprs) replaceExpr(e, map);
                    break;
                default:
                    break;
            }
        }
    }

    void replaceExpr(ast::Expr* e,
                     const std::unordered_map<std::string, std::string>& map) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Call:
                if (e->a && e->a->kind == ast::EK::Name) {
                    auto it = map.find(e->a->text);
                    if (it != map.end()) e->a->text = it->second;
                }
                replaceExpr(e->a, map);
                for (ast::Expr* a : e->args) replaceExpr(a, map);
                break;
            case ast::EK::MCall:
                replaceExpr(e->a, map);
                for (ast::Expr* a : e->args) replaceExpr(a, map);
                break;
            case ast::EK::Func:
                replaceCalls(e->fn->body, map);
                break;
            case ast::EK::Bin:
                replaceExpr(e->a, map); replaceExpr(e->b, map);
                break;
            case ast::EK::Un:
                replaceExpr(e->a, map);
                break;
            case ast::EK::Index:
                replaceExpr(e->a, map); replaceExpr(e->b, map);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) replaceExpr(f.keyExpr, map);
                    replaceExpr(f.value, map);
                }
                break;
            default:
                break;
        }
    }
};

}

void runProxyPass(ast::Chunk& chunk, PassContext& ctx) {
    ProxyPass p(ctx, ctx.cfg.proxyChance, 10);
    p.run(chunk);
    ctx.stats.proxies = p.proxies();
}

}
}
