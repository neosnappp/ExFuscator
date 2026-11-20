#pragma once

#include "astra/Config.hpp"
#include "astra/passes/Pass.hpp"

namespace astra {

struct ObfuscatorResult {
    std::string output;
    passes::Stats stats;
    size_t inputSize = 0;
    size_t outputSize = 0;
};

class Obfuscator {
public:
    explicit Obfuscator(const Config& cfg);

    ObfuscatorResult run();

private:
    Config cfg_;

    std::string buildPrologue(const passes::PassContext& ctx) const;
    std::string buildWatermark() const;
};

}
