#pragma once

#include "astra/Config.hpp"
#include "astra/Random.hpp"
#include "astra/NameGen.hpp"
#include "astra/parser/Ast.hpp"

namespace astra {
namespace passes {

struct Stats {
    int localsRenamed = 0;
    int globalsRenamed = 0;
    int stringsEncrypted = 0;
    int numbersEncoded = 0;
    int deadBlocks = 0;
    int flattenBlocks = 0;
    int cfgRegions = 0;
    int cfgStates = 0;
    int cfgBogus = 0;
    int proxies = 0;
    int opaqueWraps = 0;
    int vmProtos = 0;
    int vmInstrs = 0;
    int vmFused = 0;
    int maskedLocals = 0;
};

struct PassContext {
    Config cfg;
    Rng rng;
    NameGen gen;
    Stats stats;

    bool decoderNeeded = false;
    std::string decoderName;

    std::vector<std::unique_ptr<ast::Expr>> exprs;
    std::vector<std::unique_ptr<ast::Stmt>> stmts;
    std::vector<std::unique_ptr<ast::Block>> blocks;
    std::vector<std::unique_ptr<ast::FuncLit>> funcs;

    PassContext(const Config& c, std::uint64_t seed, std::unordered_set<std::string> avoid)
        : cfg(c), rng(seed), gen(std::move(avoid)) {}

    ast::Expr* ex(ast::EK k, int line = 0) {
        auto e = std::make_unique<ast::Expr>(k);
        e->line = line;
        exprs.push_back(std::move(e));
        return exprs.back().get();
    }
    ast::Stmt* st(ast::Stmt::K k, int line = 0) {
        auto s = std::make_unique<ast::Stmt>(k);
        s->line = line;
        stmts.push_back(std::move(s));
        return stmts.back().get();
    }
    ast::Block* blk() {
        blocks.push_back(std::make_unique<ast::Block>());
        return blocks.back().get();
    }
    ast::FuncLit* fn(int line = 0) {
        auto f = std::make_unique<ast::FuncLit>();
        f->line = line;
        funcs.push_back(std::move(f));
        return funcs.back().get();
    }

    ast::Expr* num(std::int64_t v, int line = 0) {
        if (v < 0) {
            ast::Expr* u = ex(ast::EK::Un, line);
            u->uop = ast::UO::Neg;
            u->a = num(-v, line);
            return u;
        }
        ast::Expr* e = ex(ast::EK::Num, line);
        e->num = (double)v;
        e->text = std::to_string(v);
        return e;
    }

    ast::Expr* str(std::string bytes, int line = 0) {
        ast::Expr* e = ex(ast::EK::Str, line);
        e->text = std::move(bytes);
        return e;
    }
};

void runRenamePass(ast::Chunk& chunk, PassContext& ctx);
void runProxyPass(ast::Chunk& chunk, PassContext& ctx);
void runOpaquePass(ast::Chunk& chunk, PassContext& ctx);
void runStringEncryptPass(ast::Chunk& chunk, PassContext& ctx);
void runNumberEncodePass(ast::Chunk& chunk, PassContext& ctx);
void runDeadCodePass(ast::Chunk& chunk, PassContext& ctx);
void runMaskPass(ast::Chunk& chunk, PassContext& ctx);

}
}
