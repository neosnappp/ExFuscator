#include "astra/passes/Pass.hpp"

namespace astra {
namespace passes {

namespace {

static std::string encryptBytes(const std::string& plain,
                                const std::string& key, int n) {
    std::string out(plain.size(), '\0');
    for (size_t j = 0; j < plain.size(); ++j) {
        int v = (unsigned char)plain[j] +
                (unsigned char)key[j % key.size()] +
                (int)(j + 1) * n;
        out[j] = (char)(((v % 256) + 256) % 256);
    }
    return out;
}

class Walker {
public:
    Walker(PassContext& ctx) : ctx_(ctx) {}

    void run(ast::Block* b) { block(b); }

private:
    PassContext& ctx_;

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
                if (!s->method.empty()) {}
                block(s->fn->body);
                break;
            case K::Return:
                for (ast::Expr*& e : s->exprs) expr(e);
                break;
            default:
                break;
        }
    }

    void expr(ast::Expr*& slot) {
        if (!slot) return;
        if (slot->kind == ast::EK::Str) {
            const std::string& plain = slot->text;
            if (plain.empty()) return;

            int keyLen = 1 + (int)ctx_.rng.range(16);
            std::string key;
            for (int i = 0; i < keyLen; ++i)
                key += (char)ctx_.rng.byte();
            int n = 1 + (int)ctx_.rng.range(255);

            std::string enc = encryptBytes(plain, key, n);

            ast::Expr* call = ctx_.ex(ast::EK::Call, slot->line);
            call->a = ctx_.ex(ast::EK::Name, slot->line);
            call->a->text = ctx_.decoderName;
            call->args.push_back(ctx_.str(enc, slot->line));
            call->args.push_back(ctx_.str(key, slot->line));
            call->args.push_back(ctx_.num(n, slot->line));

            slot = call;
            ++ctx_.stats.stringsEncrypted;
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
};

}

void runStringEncryptPass(ast::Chunk& chunk, PassContext& ctx) {
    if (!ctx.cfg.encryptStrings) return;
    ctx.decoderName = ctx.gen.next();
    ctx.decoderNeeded = true;
    Walker w(ctx);
    w.run(chunk.root);
}

}
}
