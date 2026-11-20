/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include "astra/Common.hpp"
#include "astra/parser/Ast.hpp"
#include "astra/vm/VmIsa.hpp"
#include "astra/vm/VmCrypto.hpp"

namespace astra {
namespace vm {

struct VmOptions {
    double opaqueChance = 0.0;
    double flattenChance = 0.0;
    double fuseChance = 0.0;
    double branchChance = 0.0;
    double decoyChance = 0.0;
    double arithChance = 0.0;
    bool shuffleBlocks = false;
    int regBaseMax = 0;
    int rotationEvery = 8192;
    bool bLayer = false;
    bool kvm = true;

    bool sandboxGlobals = true;
};

VmIR compileVmIR(ast::Chunk& chunk, std::uint64_t seed, const VmOptions& opt);

void runVmPasses(VmIR& ir, std::uint64_t seed, const VmOptions& opt);

void dumpVmIR(const VmIR& ir, std::ostream& os);

}
}
