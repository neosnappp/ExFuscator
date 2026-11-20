#include "astra/passes/Pass.hpp"

namespace astra {
namespace passes {

namespace {

using K = ast::Stmt::K;

class OpaquePass {
public:
    OpaquePass(PassContext& ctx, double chance) : ctx_(ctx), chance_(chance) {}

    void run(ast::Chunk& chunk) {
        wrapBlock(chunk.root);
    }

    int wraps() const { return wraps_; }

private:
    PassContext& ctx_;
    double chance_;
    int wraps_ = 0;

    ast::Expr* tautology() {
        int kind = (int)ctx_.rng.range(4);
        ast::Expr* e = ctx_.ex(ast::EK::Bin);
        switch (kind) {
            case 0: {

                std::int64_t m = ctx_.rng.irange(3, 999983);
                std::int64_t a = ctx_.rng.irange(-99999, 999999);
                std::int64_t b = ctx_.rng.irange(-99999, 999999);
                ast::Expr* mul = ctx_.ex(ast::EK::Bin);
                mul->op = ast::SO::Mul;
                mul->a = ctx_.num(a);
                mul->b = ctx_.num(b);
                ast::Expr* mod = ctx_.ex(ast::EK::Bin);
                mod->op = ast::SO::Mod;
                mod->a = mul;
                mod->b = ctx_.num(m);
                e->op = ast::SO::Lt;
                e->a = mod;
                e->b = ctx_.num(m);
                break;
            }
            case 1: {

                std::int64_t k = ctx_.rng.irange(-99999, 999999);
                ast::Expr* sq = ctx_.ex(ast::EK::Bin);
                sq->op = ast::SO::Mul;
                sq->a = ctx_.num(k);
                sq->b = ctx_.num(k);
                e->op = ast::SO::Ge;
                e->a = sq;
                e->b = ctx_.num(k);
                break;
            }
            case 2: {

                std::int64_t a = ctx_.rng.irange(-999999, 999999);
                std::int64_t b = ctx_.rng.irange(-999999, 999999);
                ast::Expr* sum = ctx_.ex(ast::EK::Bin);
                sum->op = ast::SO::Add;
                sum->a = ctx_.num(a);
                sum->b = ctx_.num(b);
                ast::Expr* sq = ctx_.ex(ast::EK::Bin);
                sq->op = ast::SO::Mul;
                sq->a = sum;
                sq->b = sum;
                e->op = ast::SO::Ge;
                e->a = sq;
                e->b = ctx_.num(0);
                break;
            }
            default: {

                std::int64_t k = ctx_.rng.irange(-999999, 999999);
                ast::Expr* mod = ctx_.ex(ast::EK::Bin);
                mod->op = ast::SO::Mod;
                mod->a = ctx_.num(k);
                mod->b = ctx_.num(2);
                e->op = ast::SO::Ne;
                e->a = mod;
                e->b = ctx_.num(2);
                break;
            }
        }
        return e;
    }

    void addJunkLocals(ast::Block* b) {
        int n = 1 + (int)ctx_.rng.range(3);
        for (int i = 0; i < n; ++i) {
            ast::Stmt* loc = ctx_.st(K::Local);
            loc->names.push_back(ctx_.gen.next());
            if (ctx_.rng.chance(0.5)) {
                loc->exprs.push_back(ctx_.num(ctx_.rng.irange(-999999, 999999)));
            } else {
                std::string junk;
                int len = 3 + (int)ctx_.rng.range(18);
                for (int k = 0; k < len; ++k)
                    junk += (char)ctx_.rng.byte();
                loc->exprs.push_back(ctx_.str(junk));
            }
            b->stats.push_back(loc);
        }
    }

    bool wrappable(ast::Stmt* s) const {
        switch (s->kind) {
            case K::Empty:
            case K::Local:
            case K::LocalFunc:
                return false;
            default:
                return true;
        }
    }

    ast::Stmt* wrapOnce(ast::Stmt* s) {
        ast::Stmt* ifs = ctx_.st(K::If, s->line);
        ast::IfClause c;
        c.cond = tautology();
        c.body = ctx_.blk();
        c.body->stats.push_back(s);
        ifs->clauses.push_back(c);
        if (ctx_.rng.chance(0.5)) {
            ifs->elseBody = ctx_.blk();
            addJunkLocals(ifs->elseBody);
        }
        ++wraps_;
        return ifs;
    }

    ast::Stmt* wrap(ast::Stmt* s) {
        ast::Stmt* out = wrapOnce(s);

        if (ctx_.rng.chance(0.22)) out = wrapOnce(out);
        return out;
    }

    void wrapBlock(ast::Block* b) {

        for (ast::Stmt* s : b->stats) wrapStmt(s);
        for (size_t i = 0; i < b->stats.size(); ++i) {
            ast::Stmt* s = b->stats[i];
            if (!wrappable(s)) continue;
            if (!ctx_.rng.chance(chance_)) continue;
            b->stats[i] = wrap(s);
        }
    }

    void wrapStmt(ast::Stmt* s) {
        switch (s->kind) {
            case K::LocalFunc:
                wrapBlock(s->fn->body);
                break;
            case K::Func:
                wrapBlock(s->fn->body);
                break;
            case K::Do:
                wrapBlock(s->body);
                break;
            case K::While:
                wrapBlock(s->body);
                break;
            case K::Repeat:
                wrapBlock(s->body);
                break;
            case K::If:
                for (ast::IfClause& c : s->clauses) wrapBlock(c.body);
                if (s->elseBody) wrapBlock(s->elseBody);
                break;
            case K::NumFor:
            case K::GenFor:
                wrapBlock(s->body);
                break;
            default:
                break;
        }
    }
};

}

void runOpaquePass(ast::Chunk& chunk, PassContext& ctx) {
    OpaquePass p(ctx, ctx.cfg.opaqueChance);
    p.run(chunk);
    ctx.stats.opaqueWraps = p.wraps();
}

}
}
