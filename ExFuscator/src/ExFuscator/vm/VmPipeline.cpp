#include "astra/vm/VmPipeline.hpp"

#include "astra/vm/VmEmitter.hpp"
#include <chrono>
#include <cstdlib>
#include <cstdio>
#include <unordered_set>

#include "astra/vm/VmSerializer.hpp"

namespace astra {
namespace vm {

VmResult runVmPipeline(ast::Chunk& chunk, std::uint64_t seed,
                       const VmOptions& opt, const std::string& watermark) {
    VmResult res;
    res.inputSize = 0;
    const bool timing = std::getenv("EXF_TIME") != nullptr;
    auto tick = [&timing]() -> double {
        if (!timing) return 0;
        return std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
    };
    double t0 = tick();

    pickBuildConsts((std::uint32_t)(((std::uint64_t)seed * 40503ull + 99991ull) %
                                    2147483646ull) + 1u);

    VmIR ir = compileVmIR(chunk, seed, opt);

    if (std::getenv("EXF_DUMP_IR")) {
        dumpVmIR(ir, std::cerr);
    }
    double t1 = tick();
    runVmPasses(ir, seed, opt);
    if (std::getenv("EXF_DUMP_IR2")) {
        dumpVmIR(ir, std::cerr);
    }
    double t2 = tick();

    for (const VProto& p : ir.protos) {
        res.protos++;
        res.instrs += p.code.size();
        if (p.flattened) res.flattened++;
    }

    VmBuild b = serializeVm(ir, seed, opt.rotationEvery, opt.bLayer, opt.kvm);
    b.totalInstr = (int)res.instrs;
    b.sandboxGlobals = opt.sandboxGlobals;

    {
        std::unordered_set<std::string> seen;
        for (const VProto& p : ir.protos) {
            for (const VInstr& in : p.code) {
                if (in.op != VOP_GETGLOBAL && in.op != VOP_SETGLOBAL &&
                    in.op != VOP_GCALL && in.op != VOP_GTAIL &&
                    in.op != VOP_GETGF)
                    continue;
                if (in.k < 1 || in.k > (int)p.ks.size()) continue;
                const VConst& kc = p.ks[(size_t)in.k - 1];
                if (kc.t != VConst::STR || kc.s.empty()) continue;
                if (seen.insert(kc.s).second) b.pinNames.push_back(kc.s);
            }
        }
    }

    for (const VProto& vp : ir.protos) {
        for (const VConst& vc : vp.ks) {
            if (vc.t == VConst::STR && vc.s == "coroutine") { b.usesCo = true; break; }
        }
        if (b.usesCo) break;
    }
    double t3 = tick();
    std::string out = emitVmOutput(b, seed, watermark);
    double t4 = tick();
    if (timing) {
        std::fprintf(stderr, "TIME codegen=%.1f passes=%.1f serialize=%.1f emit=%.1f total=%.1f\n",
                     t1 - t0, t2 - t1, t3 - t2, t4 - t3, t4 - t0);
    }

    res.output = out;
    res.outputSize = out.size();
    return res;
}

}
}
