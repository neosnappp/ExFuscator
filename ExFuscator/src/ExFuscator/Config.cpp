/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/

#include "astra/Config.hpp"

namespace astra {

Config Config::fromArgs(int argc, char** argv, bool& ok) {
    Config c;
    ok = true;
    std::vector<std::string> pos;

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--preset" && i + 1 < argc) c.preset = argv[++i];
    }
    c.applyPreset();

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        auto next = [&](const char* what) -> std::string {
            if (i + 1 >= argc) {
                std::cerr << "error: missing value for " << what << "\n";
                ok = false;
                return "";
            }
            return argv[++i];
        };

        if (a == "-h" || a == "--help") { c.showHelp = true; return c; }
        else if (a == "--preset") { if (i + 1 < argc) ++i; continue; }
        else if (a == "-q" || a == "--quiet") c.quiet = true;
        else if (a == "-o" || a == "--output") c.outputFile = next("--output");
        else if (a == "--seed") {
            c.seed = std::strtoull(next("--seed").c_str(), nullptr, 10);
            c.seedSet = true;
        }
        else if (a == "--no-strings") c.encryptStrings = false;
        else if (a == "--no-numbers") c.encodeNumbers = false;
        else if (a == "--no-rename") c.renameLocals = false;
        else if (a == "--no-deadcode") c.injectDeadCode = false;
        else if (a == "--no-flatten") c.flattenControlFlow = false;
        else if (a == "--no-proxies") c.useProxies = false;
        else if (a == "--no-opaque") c.opaqueWrap = false;
        else if (a == "--no-dfm") c.dataMask = false;
        else if (a == "--no-watermark") c.watermark = false;
        else if (a == "--rename-globals") c.renameGlobals = true;
        else if (a == "--vm") c.useVm = true;
        else if (a == "--globals-real") c.sandboxGlobals = false;
        else if (a.rfind("-", 0) == 0) {
            std::cerr << "error: unknown option '" << a << "'\n";
            ok = false;
        }
        else pos.push_back(a);
    }

    if (!ok) return c;
    if (pos.empty() && !c.showHelp) {
        std::cerr << "error: no input file\n";
        ok = false;
        return c;
    }
    if (!pos.empty()) c.inputFile = pos[0];

    return c;
}

void Config::applyPreset() {
    if (preset == "light") {
        dataMask = false;
        renameLocals = true;
        renameGlobals = false;
        encryptStrings = false;
        encodeNumbers = false;
        injectDeadCode = false;
        flattenControlFlow = false;
        useProxies = false;
        opaqueWrap = false;
        useVm = true;
    } else if (preset == "medium") {
        renameLocals = true;
        renameGlobals = false;
        encryptStrings = true;
        encodeNumbers = true;
        injectDeadCode = false;
        flattenControlFlow = true;
        useProxies = true;
        proxyChance = 0.5;
        opaqueWrap = true;
        opaqueChance = 0.08;
        useVm = true;
    } else if (preset == "maximum") {
        renameLocals = true;
        renameGlobals = true;
        encryptStrings = true;
        encodeNumbers = true;
        injectDeadCode = true;
        deadCodeChance = 0.28;
        flattenControlFlow = true;
        useProxies = true;
        proxyChance = 0.85;
        opaqueWrap = true;
        opaqueChance = 0.30;
        useVm = true;
    } else {
        std::cerr << "error: unknown preset '" << preset
                  << "' (use light | medium | maximum)\n";
        std::exit(1);
    }
}

}
