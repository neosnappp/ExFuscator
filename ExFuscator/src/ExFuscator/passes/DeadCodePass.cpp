#include "astra/passes/Pass.hpp"

namespace astra {
namespace passes {

namespace {

class Injector {
public:
    explicit Injector(PassContext& ctx) : ctx_(ctx) {}

    void run(ast::Block* root) {
        block(root);
    }

private:
    PassContext& ctx_;

    ast::Stmt* makeJunkBranch() {

        std::int64_t a = ctx_.rng.irange(1000, 999999);
        std::int64_t b = ctx_.rng.irange(1000, 999999);
        while (a == b) b = ctx_.rng.irange(1000, 999999);

        ast::Expr* cond = ctx_.ex(ast::EK::Bin);
        cond->op = ctx_.rng.chance(0.5) ? ast::SO::Eq : ast::SO::Gt;
        if (cond->op == ast::SO::Eq) {
            cond->a = ctx_.num(a);
            cond->b = ctx_.num(b);
        } else {
            cond->op = ast::SO::Gt;
            cond->a = ctx_.num(std::min(a, b));
            cond->b = ctx_.num(std::max(a, b));
        }

        ast::Stmt* junkIf = ctx_.st(ast::Stmt::K::If);
        ast::IfClause c;
        c.cond = cond;
        c.body = ctx_.blk();

        int junkCount = 1 + (int)ctx_.rng.range(3);
        for (int i = 0; i < junkCount; ++i) {
            ast::Stmt* loc = ctx_.st(ast::Stmt::K::Local);
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
            c.body->stats.push_back(loc);
        }
        junkIf->clauses.push_back(c);
        ++ctx_.stats.deadBlocks;
        return junkIf;
    }

    void block(ast::Block* b) {

        for (ast::Stmt* s : b->stats) stmt(s);

        size_t limit = 0;
        while (limit < b->stats.size()) {
            ast::Stmt::K k = b->stats[limit]->kind;
            if (k == ast::Stmt::K::Return || k == ast::Stmt::K::Break ||
                k == ast::Stmt::K::Continue)
                break;
            ++limit;
        }
        if (limit > 0 && ctx_.rng.chance(ctx_.cfg.deadCodeChance)) {
            size_t at = (size_t)ctx_.rng.range(limit + 1);
            b->stats.insert(b->stats.begin() + at, makeJunkBranch());
        }
    }

    void stmt(ast::Stmt* s) {
        using K = ast::Stmt::K;
        switch (s->kind) {
            case K::LocalFunc:
                block(s->fn->body);
                break;
            case K::Do:
                block(s->body);
                break;
            case K::While:
                block(s->body);
                break;
            case K::Repeat:
                block(s->body);
                break;
            case K::If:
                for (ast::IfClause& c : s->clauses) block(c.body);
                if (s->elseBody) block(s->elseBody);
                break;
            case K::NumFor:
            case K::GenFor:
                block(s->body);
                break;
            case K::Func:
                block(s->fn->body);
                break;
            default:
                break;
        }
    }
};

}

void runDeadCodePass(ast::Chunk& chunk, PassContext& ctx) {
    if (!ctx.cfg.injectDeadCode) return;
    Injector w(ctx);
    w.run(chunk.root);
}

}
}
