#pragma once

#include "astra/vm/VmIsa.hpp"
#include "astra/vm/VmCrypto.hpp"

namespace astra {
namespace vm {

struct VmBuild {
    std::string blob;

    std::string sig;
    std::string foldView;
    std::string kFoldView;
    std::string kFoldViewG;
    std::vector<int> opId;
    std::vector<int> opLayout;
    std::vector<int> decoyIds;
    std::uint32_t buildSeed = 0;
    std::uint32_t blobSalt = 0;
    std::uint32_t digest = 0;
    std::uint32_t sc1 = 0, sc2 = 0, sc3 = 0;
    std::uint32_t poolKey = 0;
    int stringsIdx = 0;
    int rotationEvery = 8192;
    int flush = 24;
    int probeEvery = 9;
    bool bLayer = false;
    bool kvm = false;
    bool usesCo = false;
    int totalInstr = 0;
    std::string kblob;
    std::uint32_t kG1 = 0;
    int kSIdx = 1;
    int kPA = 1, kPB = 2, kPC = 3;
    int kPS = 4, kPK = 5;
    int kLay = 0;
    int kW = 5;
    int kSlot = 0;
    std::vector<int> kOpIds;
    std::string ghostBlob;
    int kSIdxG = 1;
    int kLayG = 0;
    int kWG = 5;
    int nsf = 0;
    int veilGate = 512;
    int veilK = 0;

    bool sandboxGlobals = true;

    std::vector<std::string> pinNames;
};

VmBuild serializeVm(const VmIR& ir, std::uint64_t seed, int rotationEvery, bool bLayer,
                    bool kvm);

}
}
