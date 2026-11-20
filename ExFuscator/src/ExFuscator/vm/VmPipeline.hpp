#pragma once

#include "astra/Common.hpp"
#include "astra/parser/Ast.hpp"
#include "astra/vm/VmCodegen.hpp"

namespace astra {
namespace vm {

struct VmResult {
    std::string output;
    size_t inputSize = 0;
    size_t outputSize = 0;
    size_t protos = 0;
    size_t instrs = 0;
    size_t flattened = 0;
    size_t fused = 0;
    size_t opaque = 0;
};

VmResult runVmPipeline(ast::Chunk& chunk, std::uint64_t seed,
                       const VmOptions& opt, const std::string& watermark);

}
}
