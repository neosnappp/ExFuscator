#include "astra/passes/Pass.hpp"

#include <cmath>

namespace astra {
namespace passes {

namespace {

static bool encodable(const ast::Expr* e) {
    if (e->kind != ast::EK::Num) return false;
    double v = e->num;
    if (!std::isfinite(v)) return false;
    if (std::fabs(v) > 4503599627370496.0) return false;
    if (v != std::floor(v)) return false;
    return true;
}

class Walker {
public:
    explicit Walker(PassContext& ctx) : ctx_(ctx) {}

    void run(ast::Block* b) { block(b); }

private:
    PassContext& ctx_;

    ast::Expr* encode(std::int64_t v, int line) {
        for (int attempt = 0; attempt < 8; ++attempt) {
            enum Form { Add, Sub, Mul };
            Form form = (Form)ctx_.rng.range(3);

            std::int64_t a = 0, b = 0;
            if (form == Add) {
                std::int64_t delta = ctx_.rng.irange(-999999, 999999);
                if (delta == 0) continue;
                a = v + delta;
                b = -delta;
                if (std::llabs(a) > (1LL << 52) || a == v || b == v) continue;
            } else if (form == Sub) {
                std::int64_t delta = ctx_.rng.irange(-999999, 999999);
                if (delta == 0) continue;
                a = v + delta;
                b = delta;
                if (std::llabs(a) > (1LL << 52) || a == v || b == v) continue;
            } else {
                std::int64_t k = ctx_.rng.irange(2, 97);
                a = v * k;
                b = k;
                if (std::llabs(a) > (1LL << 52) || a == v || b == v) continue;
            }

            ast::Expr* bin = ctx_.ex(ast::EK::Bin, line);

            bin->op = form == Add ? ast::SO::Add
                    : form == Sub ? ast::SO::Sub
                                  : ast::SO::Div;
            bin->a = ctx_.num(a, line);
            bin->b = ctx_.num(b, line);

            if (ctx_.rng.chance(0.45)) {
                std::int64_t d2 = ctx_.rng.irange(-99999, 99999);
                if (d2 != 0 && std::llabs(a + d2) <= (1LL << 52) && (a + d2) != v) {
                    bool useAdd = ctx_.rng.chance(0.5);
                    bin->a = ctx_.ex(ast::EK::Bin, line);
                    ast::Expr* inner = bin->a;
                    inner->op = useAdd ? ast::SO::Add : ast::SO::Sub;
                    inner->a = ctx_.num(useAdd ? a - d2 : a + d2, line);
                    inner->b = ctx_.num(d2, line);
                }
            }
            return bin;
        }
        return nullptr;
    }

    void expr(ast::Expr*& slot) {
        if (!slot) return;
        if (encodable(slot)) {
            std::int64_t v = (std::int64_t)slot->num;
            if (ast::Expr* rep = encode(v, slot->line)) {
                slot = rep;
                ++ctx_.stats.numbersEncoded;
                return;
            }
            return;
        }
        switch (slot->kind) {
            case ast::EK::Bin:
                expr(slot->a); expr(slot->b);
                break;
            case ast::EK::Un:
                expr(slot->a);
                break;
            case ast::EK::Call:
            case ast::EK::MCall:
                expr(slot->a);
                for (ast::Expr*& a : slot->args) expr(a);
                break;
            case ast::EK::Index:
                expr(slot->a); expr(slot->b);
                break;
            case ast::EK::Table:
                for (ast::TableField& f : slot->fields) {
                    if (f.keyExpr) expr(f.keyExpr);
                    expr(f.value);
                }
                break;
            case ast::EK::Func:
                block(slot->fn->body);
                break;
            default:
                break;
        }
    }

    void block(ast::Block* b) {
        for (ast::Stmt* s : b->stats) stmt(s);
    }

    void stmt(ast::Stmt* s) {
        using K = ast::Stmt::K;
        switch (s->kind) {
            case K::Local:
                for (ast::Expr*& e : s->exprs) expr(e);
                break;
            case K::LocalFunc:
                block(s->fn->body);
                break;
            case K::Assign:
                for (ast::Expr*& e : s->targets) expr(e);
                for (ast::Expr*& e : s->exprs) expr(e);
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
                block(s->body);
                expr(s->exprs[0]);
                break;
            case K::If:
                for (ast::IfClause& c : s->clauses) {
                    expr(c.cond);
                    block(c.body);
                }
                if (s->elseBody) block(s->elseBody);
                break;
            case K::NumFor:
                for (ast::Expr*& e : s->exprs) expr(e);
                block(s->body);
                break;
            case K::GenFor:
                for (ast::Expr*& e : s->exprs) expr(e);
                block(s->body);
                break;
            case K::Func:
                block(s->fn->body);
                break;
            case K::Return:
                for (ast::Expr*& e : s->exprs) expr(e);
                break;
            default:
                break;
        }
    }
};

}

void runNumberEncodePass(ast::Chunk& chunk, PassContext& ctx) {
    if (!ctx.cfg.encodeNumbers) return;
    Walker w(ctx);
    w.run(chunk.root);
}

}
}
