#include "astra/passes/Pass.hpp"

#include <cmath>
#include <unordered_map>
#include <vector>

namespace astra {
namespace passes {

namespace {

struct Sym {
    std::string name;
    bool candidate = true;
    bool hasInit = false;
    bool loopRef = false;
    bool badAssign = false;
    std::vector<ast::Expr*> assigns;
    bool numeric = true;
    bool eligible = false;
    double key = 0.0;
};

bool arithOp(ast::SO op) {
    switch (op) {
        case ast::SO::Add: case ast::SO::Sub: case ast::SO::Mul:
        case ast::SO::Div: case ast::SO::IDiv: case ast::SO::Mod:
        case ast::SO::Pow:
            return true;
        default:
            return false;
    }
}

class Pass {
public:
    explicit Pass(PassContext& ctx) : ctx_(ctx) {}

    void run(ast::Chunk& chunk) {
        scopes_.push_back({});
        collect(chunk.root);
        for (int it = 0; it < 16; ++it) {
            bool changed = false;
            for (Sym* s : syms_) {
                bool ok = s->candidate && s->hasInit && !s->loopRef && !s->badAssign;
                if (ok) {
                    for (ast::Expr* e : s->assigns)
                        if (!pure(e)) { ok = false; break; }
                }
                if (ok != s->numeric) { s->numeric = ok; changed = true; }
            }
            if (!changed) break;
        }
        for (Sym* s : syms_) {
            s->eligible = s->numeric;
            if (s->eligible) {
                s->key = (double)ctx_.rng.irange(1048576, 2097151);
                ctx_.stats.maskedLocals++;
            }
        }
        if (ctx_.stats.maskedLocals > 0)
            xform(chunk.root);
        scopes_.pop_back();
    }

private:
    PassContext& ctx_;
    std::vector<std::unordered_map<std::string, Sym*>> scopes_;
    std::vector<Sym*> syms_;
    int loopDepth_ = 0;
    bool collectPhase_ = true;
    std::unordered_map<ast::Stmt*, std::vector<Sym*>> stmtSyms_;
    std::unordered_map<ast::FuncLit*, std::vector<Sym*>> paramSyms_;
    std::unordered_map<ast::Stmt*, Sym*> forVar_;

    Sym* declare(const std::string& n, bool candidate) {
        Sym* s = new Sym();
        s->name = n;
        s->candidate = candidate;
        scopes_.back()[n] = s;
        syms_.push_back(s);
        return s;
    }

    void bind(ast::Stmt* st, Sym* s) {
        scopes_.back()[s->name] = s;
        if (collectPhase_) stmtSyms_[st].push_back(s);
    }

    void bindParams(ast::FuncLit* f, const std::vector<std::string>& params) {
        std::vector<Sym*>& v = paramSyms_[f];
        if (collectPhase_) {
            for (const std::string& p : params) v.push_back(declare(p, false));
        } else {
            for (Sym* s : v) scopes_.back()[s->name] = s;
        }
    }

    Sym* resolve(const std::string& n) {
        for (size_t i = scopes_.size(); i-- > 0;) {
            auto it = scopes_[i].find(n);
            if (it != scopes_[i].end()) return it->second;
        }
        return nullptr;
    }

    bool pure(ast::Expr* e) {
        if (!e) return false;
        switch (e->kind) {
            case ast::EK::Num:

                return e->num == std::floor(e->num) && std::fabs(e->num) < 281474976710656.0 &&
                       e->num != 0.0;
            case ast::EK::Un:
                return e->uop == ast::UO::Neg && pure(e->a);
            case ast::EK::Bin:

                return (e->op == ast::SO::Add || e->op == ast::SO::Sub ||
                        e->op == ast::SO::Mod || e->op == ast::SO::IDiv) &&
                       pure(e->a) && pure(e->b);
            case ast::EK::Name: {
                Sym* s = resolve(e->text);
                return s && s->candidate && s->numeric;
            }
            default:
                return false;
        }
    }

    void touch(Sym* s) {
        if (s && loopDepth_ > 0) s->loopRef = true;
    }

    void collectExpr(ast::Expr* e) {
        if (!e) return;
        switch (e->kind) {
            case ast::EK::Name: {
                Sym* s = resolve(e->text);
                touch(s);
                break;
            }
            case ast::EK::Un:
                collectExpr(e->a);
                break;
            case ast::EK::Bin:
                collectExpr(e->a);
                collectExpr(e->b);
                break;
            case ast::EK::Call:
                collectExpr(e->a);
                for (ast::Expr* a : e->args) collectExpr(a);
                break;
            case ast::EK::MCall:
                collectExpr(e->a);
                for (ast::Expr* a : e->args) collectExpr(a);
                break;
            case ast::EK::Index:
                collectExpr(e->a);
                collectExpr(e->b);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyKind == ast::TableField::KK::ExprK) collectExpr(f.keyExpr);
                    collectExpr(f.value);
                }
                break;
            case ast::EK::Func:
                scopes_.push_back({});
                bindParams(e->fn, e->fn->params);
                collect(e->fn->body);
                scopes_.pop_back();
                break;
            default:
                break;
        }
    }

    void collect(ast::Block* b) {
        if (!b) return;
        for (ast::Stmt* st : b->stats) {
            switch (st->kind) {
                case ast::Stmt::K::Local: {
                    bool aligned = st->names.size() <= st->exprs.size();
                    if (st->exprs.size() == 1 && st->names.size() > 1) aligned = false;
                    for (size_t k = 0; k < st->exprs.size(); ++k) collectExpr(st->exprs[k]);
                    for (size_t k = 0; k < st->names.size(); ++k) {
                        Sym* s = declare(st->names[k], true);
                        bind(st, s);
                        if (!aligned || k >= st->exprs.size()) {
                            s->candidate = false;
                        } else {
                            s->hasInit = true;
                            s->assigns.push_back(st->exprs[k]);
                        }
                    }
                    break;
                }
                case ast::Stmt::K::LocalFunc: {
                    Sym* s = declare(st->names[0], false);
                    bind(st, s);
                    scopes_.push_back({});
                    bindParams(st->fn, st->fn->params);
                    collect(st->fn->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Assign: {
                    if (st->targets.size() != 1 || st->exprs.size() != 1) {
                        for (ast::Expr* t : st->targets) {
                            if (t->kind == ast::EK::Name) {
                                Sym* s = resolve(t->text);
                                if (s) s->badAssign = true;
                            }
                        }
                        for (ast::Expr* t : st->targets) collectExpr(t);
                        for (ast::Expr* e : st->exprs) collectExpr(e);
                    } else {
                        if (st->targets[0]->kind == ast::EK::Name) {
                            Sym* s = resolve(st->targets[0]->text);
                            collectExpr(st->exprs[0]);
                            if (s && s->candidate) s->assigns.push_back(st->exprs[0]);
                            else if (s) touch(s);
                        } else {
                            collectExpr(st->targets[0]);
                            collectExpr(st->exprs[0]);
                        }
                    }
                    break;
                }
                case ast::Stmt::K::Call:
                    collectExpr(st->call);
                    break;
                case ast::Stmt::K::Do:
                    scopes_.push_back({});
                    collect(st->body);
                    scopes_.pop_back();
                    break;
                case ast::Stmt::K::While: {
                    collectExpr(st->exprs[0]);
                    scopes_.push_back({});
                    loopDepth_++;
                    collect(st->body);
                    loopDepth_--;
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Repeat: {
                    scopes_.push_back({});
                    loopDepth_++;
                    collect(st->body);
                    collectExpr(st->exprs[0]);
                    loopDepth_--;
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::If: {
                    for (ast::IfClause& c : st->clauses) {
                        collectExpr(c.cond);
                        scopes_.push_back({});
                        collect(c.body);
                        scopes_.pop_back();
                    }
                    if (st->elseBody) {
                        scopes_.push_back({});
                        collect(st->elseBody);
                        scopes_.pop_back();
                    }
                    break;
                }
                case ast::Stmt::K::NumFor: {
                    for (ast::Expr* e : st->exprs) collectExpr(e);
                    scopes_.push_back({});
                    Sym* s = declare(st->names[0], false);
                    forVar_[st] = s;
                    loopDepth_++;
                    collect(st->body);
                    loopDepth_--;
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::GenFor: {
                    for (ast::Expr* e : st->exprs) collectExpr(e);
                    scopes_.push_back({});
                    for (const std::string& n : st->names) bind(st, declare(n, false));
                    loopDepth_++;
                    collect(st->body);
                    loopDepth_--;
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Func: {
                    scopes_.push_back({});
                    bindParams(st->fn, st->fn->params);
                    collect(st->fn->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Return: {
                    for (ast::Expr* e : st->exprs) collectExpr(e);
                    break;
                }
                default:
                    break;
            }
        }
    }

    ast::Expr* xformExpr(ast::Expr* e) {
        if (!e) return nullptr;
        switch (e->kind) {
            case ast::EK::Name: {
                Sym* s = resolve(e->text);
                if (s && s->eligible) {
                    ast::Expr* bin = ctx_.ex(ast::EK::Bin, e->line);
                    bin->op = ast::SO::Sub;
                    bin->a = e;
                    bin->b = ctx_.num((std::int64_t)s->key, e->line);
                    bin->paren = true;
                    return bin;
                }
                return e;
            }
            case ast::EK::Un:
                e->a = xformExpr(e->a);
                return e;
            case ast::EK::Bin:
                e->a = xformExpr(e->a);
                e->b = xformExpr(e->b);
                return e;
            case ast::EK::Call:
                e->a = xformExpr(e->a);
                for (size_t i = 0; i < e->args.size(); ++i)
                    e->args[i] = xformExpr(e->args[i]);
                return e;
            case ast::EK::MCall:
                e->a = xformExpr(e->a);
                for (size_t i = 0; i < e->args.size(); ++i)
                    e->args[i] = xformExpr(e->args[i]);
                return e;
            case ast::EK::Index:
                e->a = xformExpr(e->a);
                e->b = xformExpr(e->b);
                return e;
            case ast::EK::Table:
                for (ast::TableField& f : e->fields) {
                    if (f.keyKind == ast::TableField::KK::ExprK)
                        f.keyExpr = xformExpr(f.keyExpr);
                    f.value = xformExpr(f.value);
                }
                return e;
            case ast::EK::Func:
                scopes_.push_back({});
                bindParams(e->fn, e->fn->params);
                xform(e->fn->body);
                scopes_.pop_back();
                return e;
            default:
                return e;
        }
    }

    void xform(ast::Block* b) {
        if (!b) return;
        for (ast::Stmt* st : b->stats) {
            switch (st->kind) {
                case ast::Stmt::K::Local: {
                    bool aligned = st->names.size() <= st->exprs.size();
                    if (st->exprs.size() == 1 && st->names.size() > 1) aligned = false;
                    for (size_t k = 0; k < st->exprs.size(); ++k)
                        st->exprs[k] = xformExpr(st->exprs[k]);
                    const std::vector<Sym*>& syms = stmtSyms_[st];
                    for (size_t k = 0; k < syms.size(); ++k) {
                        Sym* s = syms[k];
                        scopes_.back()[s->name] = s;
                        if (!aligned || k >= st->exprs.size()) continue;
                        if (s->eligible) {
                            ast::Expr* bin = ctx_.ex(ast::EK::Bin, st->line);
                            bin->op = ast::SO::Add;
                            bin->a = st->exprs[k];
                            bin->b = ctx_.num((std::int64_t)s->key, st->line);
                            bin->paren = true;
                            st->exprs[k] = bin;
                        }
                    }
                    break;
                }
                case ast::Stmt::K::LocalFunc: {
                    scopes_.push_back({});
                    bindParams(st->fn, st->fn->params);
                    xform(st->fn->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Assign: {
                    if (st->targets.size() == 1 && st->exprs.size() == 1) {
                        if (st->targets[0]->kind == ast::EK::Name) {
                            Sym* s = resolve(st->targets[0]->text);
                            st->exprs[0] = xformExpr(st->exprs[0]);
                            if (s && s->eligible) {
                                ast::Expr* bin = ctx_.ex(ast::EK::Bin, st->line);
                                bin->op = ast::SO::Add;
                                bin->a = st->exprs[0];
                                bin->b = ctx_.num((std::int64_t)s->key, st->line);
                                bin->paren = true;
                                st->exprs[0] = bin;
                            }
                        } else {
                            st->targets[0] = xformExpr(st->targets[0]);
                            st->exprs[0] = xformExpr(st->exprs[0]);
                        }
                    } else {
                        for (ast::Expr*& t : st->targets) t = xformExpr(t);
                        for (ast::Expr*& e : st->exprs) e = xformExpr(e);
                    }
                    break;
                }
                case ast::Stmt::K::Call:
                    st->call = xformExpr(st->call);
                    break;
                case ast::Stmt::K::Do:
                    scopes_.push_back({});
                    xform(st->body);
                    scopes_.pop_back();
                    break;
                case ast::Stmt::K::While: {
                    st->exprs[0] = xformExpr(st->exprs[0]);
                    scopes_.push_back({});
                    xform(st->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Repeat: {
                    scopes_.push_back({});
                    xform(st->body);
                    st->exprs[0] = xformExpr(st->exprs[0]);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::If: {
                    for (ast::IfClause& c : st->clauses) {
                        c.cond = xformExpr(c.cond);
                        scopes_.push_back({});
                        xform(c.body);
                        scopes_.pop_back();
                    }
                    if (st->elseBody) {
                        scopes_.push_back({});
                        xform(st->elseBody);
                        scopes_.pop_back();
                    }
                    break;
                }
                case ast::Stmt::K::NumFor: {
                    for (ast::Expr*& e : st->exprs) e = xformExpr(e);
                    scopes_.push_back({});
                    scopes_.back()[forVar_[st]->name] = forVar_[st];
                    xform(st->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::GenFor: {
                    for (ast::Expr*& e : st->exprs) e = xformExpr(e);
                    scopes_.push_back({});
                    for (Sym* s : stmtSyms_[st]) scopes_.back()[s->name] = s;
                    xform(st->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Func: {
                    scopes_.push_back({});
                    bindParams(st->fn, st->fn->params);
                    xform(st->fn->body);
                    scopes_.pop_back();
                    break;
                }
                case ast::Stmt::K::Return: {
                    for (ast::Expr*& e : st->exprs) e = xformExpr(e);
                    break;
                }
                default:
                    break;
            }
        }
    }
};

}

void runMaskPass(ast::Chunk& chunk, PassContext& ctx) {
    Pass p(ctx);
    p.run(chunk);
}

}
}
