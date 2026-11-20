#include "astra/core/Obfuscator.hpp"
#include "astra/Diagnostic.hpp"
#include "astra/lexer/Lexer.hpp"
#include "astra/parser/Parser.hpp"
#include "astra/emitter/Emitter.hpp"
#include "astra/cff/CfgFlow.hpp"
#include "astra/vm/VmPipeline.hpp"

#include <chrono>
#include <cstdio>
#include <cstdlib>

namespace astra {

Obfuscator::Obfuscator(const Config& cfg) : cfg_(cfg) {}

std::string Obfuscator::buildWatermark() const {
    return "";
}

std::string Obfuscator::buildPrologue(const passes::PassContext& ctx) const {
    if (!ctx.decoderNeeded) return "";
    const std::string& d = ctx.decoderName;

    std::ostringstream os;
    os << "local " << d << "=function(d,k,n)"
       << "local t={}for i=1,#d do "
       << "t[i]=string.char((string.byte(d,i)-string.byte(k,(i-1)%#k+1)-i*n)%256) "
       << "end;return table.concat(t)end;";
    return os.str();
}

ObfuscatorResult Obfuscator::run() {

    std::ifstream in(cfg_.inputFile, std::ios::binary);
    if (!in)
        throw AstraError("cannot open input file: " + cfg_.inputFile);
    std::ostringstream ss;
    ss << in.rdbuf();
    std::string source = ss.str();

    ObfuscatorResult result;
    result.inputSize = source.size();

    std::uint64_t seed = cfg_.seed;
    if (!cfg_.seedSet) {
        seed = (std::uint64_t)std::chrono::steady_clock::now().time_since_epoch().count()
             ^ (std::uint64_t)(uintptr_t)&result;
        cfg_.seed = seed;
    }

    const bool timing0 = std::getenv("EXF_TIME") != nullptr;
    auto tick0 = [&timing0]() -> double {
        if (!timing0) return 0;
        return std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
    };
    double f0 = tick0();
    Lexer lexer(std::move(source), cfg_.inputFile);
    std::vector<Token> toks = lexer.tokenize();
    double f1 = tick0();

    std::unordered_set<std::string> sourceNames;
    if (!cfg_.useVm) {
        sourceNames.reserve(toks.size());
        for (const Token& t : toks)
            if (t.type == TokType::Name) sourceNames.insert(t.text);
    }

    Parser parser(std::move(toks));
    ast::Chunk chunk = parser.parse();
    double f2 = tick0();

    passes::PassContext ctx(cfg_, seed, std::move(sourceNames));
    if (cfg_.dataMask)
        passes::runMaskPass(chunk, ctx);

    int cffLevel = -1;
    if (cfg_.flattenControlFlow) {
        cffLevel = cfg_.cffLevel >= 0 ? cfg_.cffLevel
                                      : cff::levelForSize(result.inputSize);
    }

    if (cfg_.useVm) {
        vm::VmOptions vopt;
        if (cfg_.preset == "maximum") {
            vopt.flattenChance = 0.95;
            vopt.opaqueChance = 0.12;
            vopt.fuseChance = 0.9;
            vopt.branchChance = 0.6;
            vopt.decoyChance = 0.12;
            vopt.arithChance = 0.45;
            vopt.shuffleBlocks = true;
            vopt.regBaseMax = 6;
            vopt.rotationEvery = 1024;
            vopt.bLayer = true;
        } else {
            vopt.flattenChance = 0.6;
            vopt.opaqueChance = 0.06;
            vopt.fuseChance = 0.6;
            vopt.branchChance = 0.35;
            vopt.decoyChance = 0.05;
            vopt.arithChance = 0.25;
            vopt.shuffleBlocks = true;
            vopt.regBaseMax = 3;
            vopt.rotationEvery = 4096;
        }
        vopt.sandboxGlobals = cfg_.sandboxGlobals;
        if (cffLevel >= 0) {
            cff::CfgStats cs = cff::runCfgFlow(
                chunk, seed ^ 0xCFF9E5C7ULL, cff::optionsForLevel(cffLevel), nullptr);
            result.stats.cfgRegions = cs.regions;
            result.stats.cfgStates = cs.states;
            result.stats.cfgBogus = cs.bogus;
        }
        vm::VmResult vr = vm::runVmPipeline(chunk, seed, vopt, buildWatermark());
        if (timing0) {
            std::fprintf(stderr, "TIME0 lex=%.1f parse=%.1f prevm=%.1f\n",
                         f1 - f0, f2 - f1, tick0() - f2);
        }
        result.output = vr.output;
        result.outputSize = vr.output.size();
        result.stats.flattenBlocks = (int)vr.flattened;
        result.stats.opaqueWraps = (int)vr.opaque;
        result.stats.vmProtos = (int)vr.protos;
        result.stats.vmInstrs = (int)vr.instrs;
        result.stats.vmFused = (int)vr.fused;
        return result;
    }

    if (cfg_.renameLocals || cfg_.renameGlobals)
        passes::runRenamePass(chunk, ctx);

    if (cffLevel >= 0) {
        cff::CfgStats cs = cff::runCfgFlow(
            chunk, seed ^ 0xCFF9E5C7ULL, cff::optionsForLevel(cffLevel), &ctx.gen);
        ctx.stats.cfgRegions = cs.regions;
        ctx.stats.cfgStates = cs.states;
        ctx.stats.cfgBogus = cs.bogus;
    }
    if (cfg_.renameLocals && cfg_.useProxies)
        passes::runProxyPass(chunk, ctx);
    if (cfg_.renameLocals && cfg_.opaqueWrap)
        passes::runOpaquePass(chunk, ctx);

    passes::runStringEncryptPass(chunk, ctx);
    passes::runNumberEncodePass(chunk, ctx);
    passes::runDeadCodePass(chunk, ctx);

    Emitter emitter;
    std::string code = emitter.emit(chunk);

    std::string out;
    if (cfg_.watermark) out += buildWatermark();
    out += buildPrologue(ctx);
    out += code;
    result.output = out;
    result.outputSize = out.size();
    result.stats = ctx.stats;
    return result;
}

}
