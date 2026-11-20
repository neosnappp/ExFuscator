/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/

#include "astra/Config.hpp"
#include "astra/core/Obfuscator.hpp"
#include "astra/Diagnostic.hpp"

#include <fstream>

namespace {

void printHelp() {
    std::cout <<
        "Exfuscator v" << astra::kVersion << " - Luau obfuscator\n"
        "\n"
        "usage:\n"
        "  exfuscator <input.lua> [options]\n"
        "\n"
        "options:\n"
        "  -o, --output <file>      output path (default: out.lua)\n"
        "      --preset <name>      light | medium (default) | maximum\n"
        "      --seed <n>           deterministic seed (reproducible builds)\n"
        "      --no-strings         disable string encryption\n"
        "      --no-numbers         disable number encoding\n"
        "      --no-rename          disable identifier renaming\n"
        "      --no-deadcode        disable dead code injection\n"
        "      --no-flatten         disable CFG control-flow transformation\n"
        "      --no-proxies         disable call proxy indirection\n"
        "      --no-opaque          disable opaque predicate wrapping (v0.2)\n"
        "      --no-dfm             disable data-flow masking\n"
        "      --rename-globals     also rename globals (advanced)\n"
        "      --globals-real       payload global writes also land in the\n"
        "                           host environment (default: writes stay in\n"
        "                           the instance-private sandbox)\n"
        "  -q, --quiet              no console output\n"
        "  -h, --help               this help\n"
        "\n"
        "presets:\n"
        "  light    rename locals + minify + ExVM virtualization (fast)\n"
        "  medium   + strings/numbers + flattening + proxies + opaque\n"
        "           + ExVM register VM (custom encrypted bytecode)\n"
        "  maximum  + global renaming + heavy dead code + aggressive\n"
        "           flattening, opaque wrapping and VM intensity\n";
}

}

int main(int argc, char** argv) {
    using namespace astra;

    bool ok = true;
    Config cfg = Config::fromArgs(argc, argv, ok);
    if (!ok) {
        std::cerr << "run with --help for usage\n";
        return 1;
    }
    if (cfg.showHelp) {
        printHelp();
        return 0;
    }

    try {
        Obfuscator ob(cfg);
        ObfuscatorResult r = ob.run();

        std::ofstream out(cfg.outputFile, std::ios::binary);
        if (!out) {
            std::cerr << "error: cannot write output file: " << cfg.outputFile << "\n";
            return 1;
        }
        out << r.output;

        if (!cfg.quiet) {
            std::cout << "Exfuscator v" << kVersion << " - done\n";
            std::cout << "  input      : " << cfg.inputFile
                      << " (" << r.inputSize << " bytes)\n";
            std::cout << "  output     : " << cfg.outputFile
                      << " (" << r.outputSize << " bytes)\n";
            std::cout << "  seed       : " << cfg.seed << "\n";
            std::cout << "  transforms :\n";
            if (cfg.renameLocals || cfg.renameGlobals)
                std::cout << "    renamed locals   : " << r.stats.localsRenamed << "\n";
            if (cfg.renameGlobals)
                std::cout << "    renamed globals  : " << r.stats.globalsRenamed << "\n";
            if (cfg.encryptStrings)
                std::cout << "    strings encrypted: " << r.stats.stringsEncrypted << "\n";
            if (cfg.encodeNumbers)
                std::cout << "    numbers encoded  : " << r.stats.numbersEncoded << "\n";
            if (cfg.dataMask)
                std::cout << "    masked locals    : " << r.stats.maskedLocals << "\n";
            if (cfg.injectDeadCode)
                std::cout << "    dead blocks      : " << r.stats.deadBlocks << "\n";
            if (cfg.flattenControlFlow) {
                std::cout << "    cfg regions      : " << r.stats.cfgRegions << "\n";
                std::cout << "    cfg states       : " << r.stats.cfgStates << "\n";
                std::cout << "    cfg bogus edges  : " << r.stats.cfgBogus << "\n";
            }
            if (cfg.useProxies && cfg.renameLocals)
                std::cout << "    call proxies     : " << r.stats.proxies << "\n";
            if (cfg.opaqueWrap && cfg.renameLocals)
                std::cout << "    opaque wraps     : " << r.stats.opaqueWraps << "\n";
            if (cfg.useVm) {
                std::cout << "    vm protos        : " << r.stats.vmProtos << "\n";
                std::cout << "    vm instructions  : " << r.stats.vmInstrs << "\n";
                std::cout << "    fused pairs      : " << r.stats.vmFused << "\n";
            }
        }
        return 0;
    } catch (const AstraError& e) {
        std::cerr << e.pretty(cfg.inputFile) << "\n";
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "internal error: " << e.what() << "\n";
        return 1;
    }
}
