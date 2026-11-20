#include "astra/passes/Pass.hpp"

namespace astra {
namespace passes {

namespace {

struct Binding {
    std::string old;
    std::string neu;
    bool isGlobal = false;
};

class Renamer {
public:
    Renamer(PassContext& ctx) : ctx_(ctx), renameGlobals_(ctx.cfg.renameGlobals) {}

    void run(ast::Block* root) {
        collectOwnedGlobals(root);
        push();
        for (ast::Stmt* s : root->stats) stmt(s);
        pop();
    }

private:
    PassContext& ctx_;
    bool renameGlobals_;
    std::vector<std::unordered_map<std::string, Binding*>> scopes_;
    std::unordered_map<std::string, Binding*> globals_;
    std::unordered_set<std::string> ownedGlobals_;
    std::vector<std::unique_ptr<Binding>> owned_;

    void collectOwnedGlobals(ast::Block* b) {
        for (ast::Stmt* s : b->stats) {
            using K = ast::Stmt::K;
            switch (s->kind) {
                case K::Assign:
                    for (ast::Expr* t : s->targets)
                        if (t->kind == ast::EK::Name) ownedGlobals_.insert(t->text);
                    for (ast::Expr* e : s->exprs) ownedScanExpr(e);
                    break;
                case K::Local:
                    for (ast::Expr* e : s->exprs) ownedScanExpr(e);
                    break;
                case K::LocalFunc:
                    ownedScanBlock(s->fn->body);
                    break;
                case K::Call:
                    ownedScanExpr(s->call);
                    break;
                case K::Do:
                    ownedScanBlock(s->body);
                    break;
                case K::While:
                    ownedScanExpr(s->exprs[0]);
                    ownedScanBlock(s->body);
                    break;
                case K::Repeat:
                    ownedScanBlock(s->body);
                    ownedScanExpr(s->exprs[0]);
                    break;
                case K::If:
                    for (ast::IfClause& c : s->clauses) {
                        ownedScanExpr(c.cond);
                        ownedScanBlock(c.body);
                    }
                    if (s->elseBody) ownedScanBlock(s->elseBody);
                    break;
                case K::NumFor:
                    for (ast::Expr* e : s->exprs) ownedScanExpr(e);
                    ownedScanBlock(s->body);
                    break;
                case K::GenFor:
                    for (ast::Expr* e : s->exprs) ownedScanExpr(e);
                    ownedScanBlock(s->body);
                    break;
                case K::Func:
                    ownedGlobals_.insert(s->path[0]);
                    ownedScanBlock(s->fn->body);
                    break;
                case K::Return:
                    for (ast::Expr* e : s->exprs) ownedScanExpr(e);
                    break;
                default:
                    break;
            }
        }
    }

    void ownedScanExpr(ast::Expr* e) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Bin:
                ownedScanExpr(e->a); ownedScanExpr(e->b);
                break;
            case ast::EK::Un:
                ownedScanExpr(e->a);
                break;
            case ast::EK::Call:
            case ast::EK::MCall:
                ownedScanExpr(e->a);
                for (ast::Expr* a : e->args) ownedScanExpr(a);
                break;
            case ast::EK::Index:
                ownedScanExpr(e->a); ownedScanExpr(e->b);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) ownedScanExpr(f.keyExpr);
                    ownedScanExpr(f.value);
                }
                break;
            case ast::EK::Func:
                ownedScanBlock(e->fn->body);
                break;
            default:
                break;
        }
    }

    void ownedScanBlock(ast::Block* b) {
        if (b) collectOwnedGlobals(b);
    }

    Binding* makeBinding(const std::string& old, bool isGlobal) {
        auto b = std::make_unique<Binding>();
        b->old = old;
        b->neu = ctx_.gen.next();
        b->isGlobal = isGlobal;
        Binding* p = b.get();
        owned_.push_back(std::move(b));
        return p;
    }

    void push() { scopes_.emplace_back(); }
    void pop() { scopes_.pop_back(); }

    Binding* declareLocal(const std::string& name) {
        Binding* b = makeBinding(name, false);
        scopes_.back()[name] = b;
        ++ctx_.stats.localsRenamed;
        return b;
    }

    Binding* declareSelf(const std::string& name) {
        auto b = std::make_unique<Binding>();
        b->old = name;
        b->neu = "self";
        b->isGlobal = false;
        Binding* p = b.get();
        owned_.push_back(std::move(b));
        ctx_.gen.reserve("self");
        scopes_.back()[name] = p;
        ++ctx_.stats.localsRenamed;
        return p;
    }

    Binding* resolve(const std::string& name) {
        for (int i = (int)scopes_.size() - 1; i >= 0; --i) {
            auto it = scopes_[i].find(name);
            if (it != scopes_[i].end()) return it->second;
        }
        if (renameGlobals_ && ownedGlobals_.count(name)) {
            Binding*& b = globals_[name];
            if (!b) {
                b = makeBinding(name, true);
                ++ctx_.stats.globalsRenamed;
            }
            return b;
        }
        return nullptr;
    }

    void bodyInCurrentScope(ast::Block* b) {
        for (ast::Stmt* s : b->stats) stmt(s);
    }

    void funcScope(ast::FuncLit* f, bool firstIsSelf = false) {
        push();
        for (size_t i = 0; i < f->params.size(); ++i) {
            std::string& p = f->params[i];
            if (firstIsSelf && i == 0) {
                p = declareSelf(p)->neu;
            } else {
                Binding* b = declareLocal(p);
                p = b->neu;
            }
        }
        bodyInCurrentScope(f->body);
        pop();
    }

    void stmt(ast::Stmt* s) {
        using K = ast::Stmt::K;
        switch (s->kind) {
            case K::Empty:
            case K::Break:
            case K::Continue:
                break;

            case K::Local:
                for (ast::Expr* e : s->exprs) expr(e);
                for (std::string& n : s->names) {
                    Binding* b = declareLocal(n);
                    n = b->neu;
                }
                break;

            case K::LocalFunc: {
                Binding* fb = declareLocal(s->names[0]);
                s->names[0] = fb->neu;
                funcScope(s->fn);
                break;
            }

            case K::Assign:
                for (ast::Expr* e : s->targets) expr(e);
                for (ast::Expr* e : s->exprs) expr(e);
                break;

            case K::Call:
                expr(s->call);
                break;

            case K::Do:
                block(s->body);
                break;

            case K::While:
                expr(s->exprs[0]);
                block(s->body);
                break;

            case K::Repeat:

                push();
                bodyInCurrentScope(s->body);
                expr(s->exprs[0]);
                pop();
                break;

            case K::If:
                for (ast::IfClause& c : s->clauses) {
                    expr(c.cond);
                    block(c.body);
                }
                if (s->elseBody) block(s->elseBody);
                break;

            case K::NumFor:
                for (ast::Expr* e : s->exprs) expr(e);
                push();
                {
                    Binding* b = declareLocal(s->names[0]);
                    s->names[0] = b->neu;
                }
                bodyInCurrentScope(s->body);
                pop();
                break;

            case K::GenFor:
                for (ast::Expr* e : s->exprs) expr(e);
                push();
                for (std::string& n : s->names) {
                    Binding* b = declareLocal(n);
                    n = b->neu;
                }
                bodyInCurrentScope(s->body);
                pop();
                break;

            case K::Func: {

                for (std::string& seg : s->path) {
                    Binding* b = resolve(seg);
                    if (b) seg = b->neu;
                }
                funcScope(s->fn, !s->method.empty());
                break;
            }

            case K::Return:
                for (ast::Expr* e : s->exprs) expr(e);
                break;
        }
    }

    void block(ast::Block* b) {
        push();
        for (ast::Stmt* s : b->stats) stmt(s);
        pop();
    }

    void expr(ast::Expr* e) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Name: {
                Binding* b = resolve(e->text);
                e->binding = b;
                if (b) e->text = b->neu;
                break;
            }
            case ast::EK::Bin:
                expr(e->a); expr(e->b);
                break;
            case ast::EK::Un:
                expr(e->a);
                break;
            case ast::EK::Call:
            case ast::EK::MCall:
                expr(e->a);
                for (ast::Expr* a : e->args) expr(a);
                break;
            case ast::EK::Index:
                expr(e->a); expr(e->b);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyExpr) expr(f.keyExpr);
                    expr(f.value);
                }
                break;
            case ast::EK::Func:
                funcScope(e->fn);
                break;
            default:
                break;
        }
    }
};

}

void runRenamePass(ast::Chunk& chunk, PassContext& ctx) {
    Renamer r(ctx);
    r.run(chunk.root);
}

}
}
