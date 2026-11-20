#pragma once

#include "astra/Common.hpp"

namespace astra {

struct Config {
    std::string inputFile;
    std::string outputFile = "out.lua";
    std::string preset = "medium";

    bool renameLocals   = true;
    bool renameGlobals  = false;
    bool encryptStrings = true;
    bool encodeNumbers  = true;
    bool injectDeadCode = true;
    bool watermark      = true;

    bool flattenControlFlow = true;
    bool useProxies         = true;
    bool opaqueWrap         = true;

    bool useVm = true;
    bool dataMask = true;

    bool sandboxGlobals = true;

    double deadCodeChance = 0.16;
    double proxyChance    = 0.5;
    double opaqueChance   = 0.12;

    int cffLevel = -1;

    std::uint64_t seed = 0;
    bool seedSet = false;
    bool quiet = false;
    bool showHelp = false;

    static Config fromArgs(int argc, char** argv, bool& ok);
    void applyPreset();
};

}
