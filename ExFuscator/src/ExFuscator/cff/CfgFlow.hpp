#pragma once

#include "astra/Common.hpp"
#include "astra/Random.hpp"
#include "astra/NameGen.hpp"
#include "astra/parser/Ast.hpp"

namespace astra {
namespace cff {

struct CfgOptions {
    double flattenChance = 1.0;
    double bogusChance = 0.0;
    double junkChance = 0.0;
    size_t minStats = 3;
    size_t minNodes = 4;
    size_t nodeBudget = 48;
};

struct CfgStats {
    int regions = 0;
    int states = 0;
    int bogus = 0;
    int dead = 0;
};

int levelForSize(size_t bytes);

CfgOptions optionsForLevel(int level);

CfgStats runCfgFlow(ast::Chunk& chunk, std::uint64_t seed, const CfgOptions& opt,
                    NameGen* sharedNames);

}
}
