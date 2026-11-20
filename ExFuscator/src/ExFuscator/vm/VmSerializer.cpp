#include "astra/vm/VmSerializer.hpp"

#include "astra/vm/Ed25519.hpp"

#include "astra/vm/Ed25519.hpp"

#include "astra/vm/VmPack.hpp"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <iomanip>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <unordered_map>
#include <unordered_set>

namespace astra {
namespace vm {

namespace {

struct W {
    std::string b;
    void u1(std::uint32_t v) { b.push_back((char)(std::uint8_t)(v & 0xFFu)); }
    void u2(std::uint32_t v) {
        b.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
        b.push_back((char)(std::uint8_t)(v & 0xFFu));
    }
    void u3(std::uint32_t v) {
        b.push_back((char)(std::uint8_t)((v >> 16) & 0xFFu));
        b.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
        b.push_back((char)(std::uint8_t)(v & 0xFFu));
    }
    void u4(std::uint32_t v) {
        b.push_back((char)(std::uint8_t)((v >> 24) & 0xFFu));
        b.push_back((char)(std::uint8_t)((v >> 16) & 0xFFu));
        b.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
        b.push_back((char)(std::uint8_t)(v & 0xFFu));
    }
    void raw(const std::string& s) { b += s; }
};

std::string numText(double v) {
    char buf[64];
    for (int p = 15; p >= 1; --p) {
        std::snprintf(buf, sizeof(buf), "%.*g", p, v);
        if (std::strtod(buf, nullptr) == v) return std::string(buf);
    }
    std::snprintf(buf, sizeof(buf), "%.17g", v);
    return std::string(buf);
}

bool ieeeEncode(double v, std::uint8_t out[8]) {
    std::uint64_t bits;
    std::memcpy(&bits, &v, 8);
    std::uint64_t E = (bits >> 52) & 0x7FFULL;
    if (E == 0x7FFULL) {

        for (int q = 0; q < 8; ++q)
            out[q] = (std::uint8_t)((bits >> (56 - 8 * q)) & 0xFFULL);
        return true;
    }
    std::uint64_t F = bits & 0xFFFFFFFFFFFFULL;
    int sgn = (int)(bits >> 63);
    double r;
    if (E == 0) r = std::ldexp((double)F, -1074);
    else r = std::ldexp((double)(F + (1ULL << 52)), (int)E - 1075);
    if (sgn) r = -r;
    std::uint64_t rb;
    std::memcpy(&rb, &r, 8);
    if (rb != bits) return false;
    for (int q = 0; q < 8; ++q)
        out[q] = (std::uint8_t)((bits >> (56 - 8 * q)) & 0xFFULL);
    return true;
}

void pushVarint(W& w, std::uint64_t m) {
    do {
        std::uint32_t b = (std::uint32_t)(m & 0x7Full);
        m >>= 7;
        if (m) b |= 0x80u;
        w.u1(b);
    } while (m);
}

}

VmBuild serializeVm(const VmIR& ir, std::uint64_t seed, int rotationEvery, bool bLayer,
                    bool kvm) {
    Rng rng(seed ^ 0x0B10B3ULL);
    VmBuild out;
    out.bLayer = bLayer;
    out.rotationEvery = rotationEvery > 0 ? rotationEvery : 4096;
    out.flush = out.rotationEvery;
    out.probeEvery = out.rotationEvery <= 2048 ? 9 : 13;

    out.buildSeed = 1 + (std::uint32_t)rng.range(kMod31 - 1);

    out.blobSalt = 1 + (std::uint32_t)rng.range(4294967294u);
    out.veilK = (int)(1 + rng.range(2147483645ull));
    const std::uint32_t envF = envFoldOf();
    out.sc1 = 1 + (std::uint32_t)rng.range(999982);
    out.sc2 = (std::uint32_t)rng.range(999982);
    out.sc3 = (out.sc1 * 3u + out.sc2) % g_bc.pr;

    const bool stiming = std::getenv("EXF_TIME") != nullptr;

    const bool dbgPp = std::getenv("EXF_PPDBG") != nullptr;
    const bool dbgVeil = std::getenv("EXF_VEILDBG") != nullptr;
    const bool dbgIs = std::getenv("EXF_ISDBG") != nullptr;
    const bool dbgOp = std::getenv("EXF_OPDBG") != nullptr;
    const bool noIsab = std::getenv("EXF_NO_ISAB") != nullptr;
    const bool dbgLay = std::getenv("EXF_LAYDBG") != nullptr;
    auto stick = [&stiming]() -> double {
        if (!stiming) return 0;
        return std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
    };
    double s0 = stick();
    double tLoop = 0, tAz = 0, tEnc = 0, tSbox = 0, tKvm = 0;
    const std::vector<std::uint8_t> sbox =
        genSbox(vaultKeyOf(out.blobSalt, out.buildSeed));

    std::vector<int> perm(VOP_COUNT);
    for (int i = 0; i < VOP_COUNT; ++i) perm[i] = i + 1;
    for (int i = VOP_COUNT - 1; i > 0; --i) {
        int j = (int)rng.range((std::uint64_t)(i + 1));
        std::swap(perm[i], perm[j]);
    }
    out.opId.assign(VOP_COUNT, 0);
    out.opLayout.assign(VOP_COUNT, 0);
    for (int i = 0; i < VOP_COUNT; ++i) {
        out.opId[i] = perm[i];
        out.opLayout[i] = (int)pickLayout(opFmtClass(i), rng);
        if (i >= VOP_DECOY0 && i <= VOP_DECOY11) out.decoyIds.push_back(perm[i]);
    }
    std::vector<int> canonOf(VOP_COUNT + 1, 0);
    for (int i = 0; i < VOP_COUNT; ++i) canonOf[out.opId[i]] = i;

    const size_t nprotos = ir.protos.size();
    std::vector<std::uint32_t> kd(nprotos);
    for (size_t i = 0; i < nprotos; ++i) kd[i] = (std::uint32_t)rng.range(kMod31 - 1);
    std::uint32_t poolDelta = (std::uint32_t)rng.range(kMod31 - 1);

    std::vector<std::string> uniq;
    std::unordered_map<std::string, int> seen;
    for (const VProto& p : ir.protos) {
        for (const VConst& c : p.ks) {
            if (c.t == VConst::STR && !seen.count(c.s)) {
                seen[c.s] = 1;
                uniq.push_back(c.s);
            }
        }
    }
    std::vector<std::string> junkPool;
    for (int d = 0; d < 4; ++d) {
        std::string s;
        int len = 3 + (int)rng.range(15);
        for (int j = 0; j < len; ++j)
            s.push_back((char)(32 + rng.range(95)));
        if (!seen.count(s)) {
            seen[s] = 1;
            uniq.push_back(s);
            junkPool.push_back(s);
        }
    }
    std::vector<std::string> pool = uniq;
    if (!pool.empty()) {
        for (size_t x = pool.size() - 1; x > 0; --x) {
            size_t j = (size_t)rng.range(x + 1);
            std::swap(pool[x], pool[j]);
        }
    }
    std::vector<std::string> poolFrag;
    std::vector<char> fragFlag;
    std::unordered_map<std::string, int> poolIdx;
    for (size_t x = 0; x < pool.size(); ++x) {
        const std::string& sRef = pool[x];
        if ((int)sRef.size() >= 5 && (int)sRef.size() <= 32000 && rng.chance(0.85)) {
            int spPos = 2 + (int)rng.range((std::uint64_t)(sRef.size() - 3));
            int idx1 = (int)poolFrag.size() + 1;
            poolFrag.push_back(sRef.substr(0, (size_t)spPos));
            fragFlag.push_back(1);
            poolFrag.push_back(sRef.substr((size_t)spPos));
            fragFlag.push_back(0);
            poolIdx[sRef] = idx1;
        } else {
            int idx1 = (int)poolFrag.size() + 1;
            poolFrag.push_back(sRef);
            fragFlag.push_back(0);
            poolIdx[sRef] = idx1;
        }
    }

    const int ndecoy = 3 + (int)rng.range(3);
    const int nfakepool = 4 + (int)rng.range(3);
    const int totalMiddle = (int)nprotos + 1 + nfakepool + ndecoy;
    struct Slot { int kind = 0; int id = 0; };
    std::vector<Slot> slots((size_t)totalMiddle);
    for (int i = 0; i < (int)nprotos; ++i) slots[(size_t)i] = {0, i};
    slots[(size_t)nprotos] = {1, 0};
    for (int d = 0; d < nfakepool; ++d) slots[(size_t)(nprotos + 1 + d)] = {3, d};
    for (int d = 0; d < ndecoy; ++d) slots[(size_t)(nprotos + 1 + nfakepool + d)] = {2, d};
    for (int i = totalMiddle - 1; i > 0; --i) {
        int j = (int)rng.range((std::uint64_t)(i + 1));
        std::swap(slots[(size_t)i], slots[(size_t)j]);
    }

    std::uint32_t anchor = (out.blobSalt + (std::uint64_t)out.buildSeed * 3ull) % kMod31;
    if (anchor < 1u) anchor += 2147483646u;

    const std::uint32_t poolBaseV = protoKeyOf(out.buildSeed, (int)nprotos + 1);

    std::vector<std::uint32_t> cs((size_t)totalMiddle + 3, 0);
    std::vector<std::string> secPay((size_t)totalMiddle + 3, std::string());
    std::vector<int> posOfProto(nprotos, -1);
    std::vector<std::uint32_t> pck(nprotos, 0);
    std::vector<int> keArr(nprotos, 0);
    bool keAny = false;
    int poolPos = -1;
    std::string afterMeta;
    std::uint32_t hdrSt = mixIdx(out.blobSalt, 4444ull);
    std::uint8_t metaHs[8];
    for (int q = 0; q < 8; ++q) {
        hdrSt = lehmer(hdrSt);
        metaHs[q] = (std::uint8_t)(hdrSt & 0xFFu);
    }

    for (int pos = 2; pos <= totalMiddle + 1; ++pos) {
        const Slot& sl = slots[(size_t)(pos - 2)];
        std::uint32_t pv = pos >= 3 ? cs[(size_t)(pos - 1)] : anchor;
        std::string payload;
        if (sl.kind == 0) {
            const int pid = sl.id;
            posOfProto[(size_t)pid] = pos;
            const VProto& p = ir.protos[(size_t)pid];
            std::uint32_t key = protoKeyOf(out.buildSeed, pid);
            key = (std::uint32_t)(((std::uint64_t)key + kd[(size_t)pid] + pv) % kMod31);
            if (key < 1u) key += 2147483646u;
            std::uint32_t veil0 = (std::uint32_t)(((std::uint64_t)key * (std::uint64_t)g_bc.mb +
                (std::uint64_t)out.veilK + (std::uint64_t)envF) % kMod31);
            if (veil0 < 1u) veil0 += 2147483646u;
            int preK = 0;
            {
                std::uint32_t ez = lehmer(mixIdx(key, (std::uint64_t)g_bc.ikP));
                int roll = (int)(ez % 100u);
                preK = roll < 35 ? 0 : (roll < 75 ? 1 : 2);
            }
            if (!keAny && preK == 0) preK = 1;
            for (int ep = 1; ep <= preK; ++ep) {
                std::uint32_t la = 3u + lehmer(mixIdx(key, (std::uint64_t)g_bc.ikV1 + (std::uint64_t)ep)) % 246u;
                std::uint32_t lb = 2u + lehmer(mixIdx(key, (std::uint64_t)g_bc.ikV2 + (std::uint64_t)ep)) % 2147483644u;
                veil0 = (std::uint32_t)(((std::uint64_t)veil0 * la + lb) % kMod31);
                if (veil0 < 1u) veil0 += 2147483646u;
            }
            keArr[(size_t)pid] = preK;
            if (preK > 0) keAny = true;
            std::vector<int> p2(VOP_COUNT + 1, 0);
            protoShuffle(p2, key);
            const std::uint32_t key2 = key2Of(key, out.blobSalt);
            std::vector<int> p2b(VOP_COUNT + 1, 0);
            std::vector<int> p2c(VOP_COUNT + 1, 0);
            if (bLayer) {
                protoShuffle(p2b, key2);
                std::uint32_t key3 = (std::uint32_t)(((std::uint64_t)key +
                    (std::uint64_t)g_bc.sb * (std::uint64_t)g_bc.ma + (std::uint64_t)g_bc.sc +
                    (std::uint64_t)g_bc.sd) % kMod31);
                if (key3 < 1u) key3 += 2147483646u;
                protoShuffle(p2c, key3);
            }
            const std::uint32_t key4 = mixIdx(key, (std::uint64_t)g_bc.ik4);
            std::vector<int> p2d(VOP_COUNT + 1, 0);

            protoShuffle(p2d, key4);
            const std::uint32_t key5 = mixIdx(key, (std::uint64_t)g_bc.ik5);
            std::vector<int> p2e(VOP_COUNT + 1, 0);
            protoShuffle(p2e, key5);
            const std::uint32_t key6 = mixIdx(key, (std::uint64_t)g_bc.ik6);
            std::vector<int> p2f(VOP_COUNT + 1, 0);
            protoShuffle(p2f, key6);
            const int isaB = noIsab ? 0 : (int)(mixIdx(key, (std::uint64_t)g_bc.ikB) % 2u);
            static const int PERM[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};
            const int ord2 = (int)(mixIdx(key, (std::uint64_t)g_bc.ikO) % 6u);
            const int nksJunkRange = 4;
            std::vector<int> kOrd;
            std::vector<int> kNew;
            std::vector<VConst> ksAll = p.ks;
            {
                const int nksJunk = (int)rng.range((std::uint64_t)nksJunkRange);
                for (int qs = 0; qs < nksJunk && !junkPool.empty(); ++qs) {
                    VConst jc2;
                    jc2.t = VConst::STR;
                    jc2.s = junkPool[(size_t)rng.range((std::uint64_t)junkPool.size())];
                    ksAll.push_back(jc2);
                }

                const int nksJnum = (int)rng.range(3);
                for (int qs = 0; qs < nksJnum; ++qs) {
                    VConst jc3;
                    int shape = (int)rng.range(4);
                    if (shape == 0) {
                        jc3.t = VConst::NUM;
                        jc3.n = (double)(100 + (int)rng.range(999999));
                    } else if (shape == 1) {
                        jc3.t = VConst::NUM;
                        jc3.n = -(double)(100 + (int)rng.range(999999));
                    } else if (shape == 2) {
                        jc3.t = VConst::NUM;
                        jc3.n = 0.5 * (double)(1 + (int)rng.range(8192));
                    } else {
                        jc3.t = VConst::BOOL;
                        jc3.b = rng.chance(0.5);
                    }
                    ksAll.push_back(jc3);
                }
            }
            const size_t nkCount = ksAll.size();
            const size_t njunk = 1 + (size_t)rng.range(3);
            if (nkCount > 0) {
                kOrd.resize(nkCount);
                std::uint32_t rot = (std::uint32_t)rng.range((std::uint64_t)nkCount);
                for (size_t t = 0; t < nkCount; ++t)
                    kOrd[t] = (int)((t + rot) % nkCount);
                kNew.assign(nkCount, 0);
                for (size_t t = 0; t < nkCount; ++t) kNew[(size_t)kOrd[t]] = (int)t;
            }
            auto remapK = [&](int kk) -> int {
                if (kk >= 1 && kk <= (int)nkCount) return kNew[(size_t)(kk - 1)] + 1;
                return kk;
            };
            const std::uint32_t km = kMaskOf(key, 251);
            const std::uint32_t afs0 = (key + g_bc.sc) % kMod31;
            const std::uint32_t afA = 3u + lehmer(afs0) % 247u;
            const std::uint32_t afB = lehmer(afs0 + g_bc.sd) % 251u;
            std::vector<int> layOpid((size_t)VOP_COUNT + 1, 0);
            {
                std::uint32_t lst = key % kMod31;
                if (lst < 1u) lst += 2147483646u;
                for (int v = 1; v <= VOP_COUNT; ++v) {
                    lst = lehmer(lst);
                    int g = out.opLayout[canonOf[v]];
                    int q = g;
                    if (g == VL_ABC4 || g == VL_BAC4)
                        q = (lst % 2u == 0u) ? VL_ABC4 : VL_BAC4;
                    else if (g == VL_AB3 || g == VL_BA3)
                        q = (lst % 2u == 0u) ? VL_AB3 : VL_BA3;
                    else if (g == VL_AK3 || g == VL_KA3)
                        q = (lst % 2u == 0u) ? VL_AK3 : VL_KA3;
                    layOpid[(size_t)v] = q;
                }
            }
            if (dbgLay) {
                std::fprintf(stderr, "LAY pid=%d key=%u lay:", pid, key);
                for (int v = 1; v < VOP_COUNT; ++v)
                    std::fprintf(stderr, " %d:%d", v, layOpid[(size_t)v]);
                std::fprintf(stderr, "\n");
            }
            std::vector<int> chAll = p.children;
            const int ndch = (int)rng.range(3);
            for (int qc = 0; qc < ndch; ++qc)
                chAll.push_back((int)rng.range((std::uint64_t)(nprotos + 2)));
            std::vector<int> hord((size_t)10, 0);
            for (int hi2 = 1; hi2 <= 9; ++hi2) hord[(size_t)hi2] = hi2;
            {
                std::uint32_t hs = (std::uint32_t)(((std::uint64_t)key * (std::uint64_t)g_bc.sd +
                    (std::uint64_t)g_bc.sc) % kMod31);
                if (hs < 1u) hs += 2147483646u;
                for (int hi2 = 9; hi2 >= 2; --hi2) {
                    hs = lehmer(hs);
                    int hj = 1 + (int)(hs % (std::uint32_t)hi2);
                    std::swap(hord[(size_t)hi2], hord[(size_t)hj]);
                }
            }
            std::uint32_t tmap[7];
            for (int ti2 = 0; ti2 < 7; ++ti2) tmap[ti2] = (std::uint32_t)ti2;
            {
                std::uint32_t tsd = (std::uint32_t)(((std::uint64_t)key + (std::uint64_t)g_bc.sb) %
                                                    kMod31);
                if (tsd < 1u) tsd += 2147483646u;
                for (int ti2 = 6; ti2 >= 1; --ti2) {
                    tsd = lehmer(tsd);
                    int tj = (int)(tsd % (std::uint32_t)(ti2 + 1));
                    std::swap(tmap[ti2], tmap[tj]);
                }
            }
            W w;

            w.b.reserve(512 + p.code.size() * 20 + ksAll.size() * 24 + chAll.size() * 8);
            for (int hi3 = 1; hi3 <= 9; ++hi3) {
                switch (hord[(size_t)hi3]) {
                    case 1: w.u2((std::uint32_t)p.nparams); break;
                    case 2: w.u1(p.vararg ? 1u : 0u); break;
                    case 3: w.u1((std::uint32_t)p.regBase); break;
                    case 4: w.u2((std::uint32_t)p.upvals.size()); break;
                    case 5: w.u2((std::uint32_t)p.nregs); break;
                    case 6: w.u2((std::uint32_t)(nkCount + njunk)); break;
                    case 7: w.u2((std::uint32_t)chAll.size()); break;
                    case 8: w.u2((std::uint32_t)p.code.size()); break;
                    default: w.u2((std::uint32_t)p.flat.size()); break;
                }
            }
            {
                int uvix = 0;
                for (const VUpval& u : p.upvals) {
                    ++uvix;
                    w.u1((std::uint32_t)u.kind);
                    std::uint32_t uvk = mixIdx(key, 400ull + (std::uint64_t)uvix);
                    w.u2((std::uint32_t)u.idx ^ (uvk >> 16));
                }
            }
            std::uint64_t chn = key;
            const auto chnLm = [&chn]() {
                chn = lehmer((std::uint32_t)chn);
            };
            const auto chnMix = [&chn](std::uint64_t u) {
                chn = (chn + (u % 2147483647ull) * (std::uint64_t)g_bc.mb) % 2147483647ull;
                if (chn < 1ull) chn += 2147483646ull;
            };
            const auto chnCi = [&chn](std::uint64_t wi) {
                return mixIdx(chn, wi);
            };
            for (size_t ki = 0; ki < nkCount; ++ki) {
                const VConst& c = ksAll[(size_t)kOrd[ki]];
                const std::uint64_t wi = ki + 1ull;
                switch (c.t) {
                    case VConst::NIL: w.u1(tmap[0]); chnLm(); break;
                    case VConst::BOOL: w.u1(c.b ? tmap[1] : tmap[2]); chnLm(); break;
                    case VConst::NUM: {
                        double nv = c.n;

                        if (std::floor(nv) == nv && std::fabs(nv) < 2147483648.0 &&
                            !(nv == 0 && std::signbit(nv))) {
                            std::uint32_t u = nv < 0
                                ? (std::uint32_t)(4294967296.0 + nv)
                                : (std::uint32_t)nv;
                            std::uint32_t ci = chnCi(wi);
                            std::uint32_t mag = u ^ ci;
                            w.u1(tmap[4]);
                            w.u1(0);
                            pushVarint(w, mag);
                            chnMix(u);
                        } else {
                            std::uint8_t fb[8];
                            if (ieeeEncode(nv, fb)) {
                                std::uint32_t ci = chnCi(wi);
                                std::uint32_t c2 = lehmer(ci);
                                const std::uint32_t xs[8] = {
                                    ci >> 24, ci >> 16, ci >> 8, ci,
                                    c2 >> 24, c2 >> 16, c2 >> 8, c2};
                                w.u1(tmap[6]);
                                for (int q = 0; q < 8; ++q)
                                    w.u1((std::uint32_t)fb[q] ^ (xs[q] & 0xFFu));
                                chnLm();
                            } else {
                                std::string t = numText(nv);
                                w.u1(tmap[3]);
                                w.u1((std::uint32_t)t.size());
                                w.raw(t);
                                chnLm();
                            }
                        }
                        break;
                    }
                    case VConst::STR:
                        w.u1(tmap[5]);
                        w.u2((std::uint32_t)poolIdx[c.s]);
                        chnLm();
                        break;
                }
            }
            for (size_t jj = 0; jj < njunk; ++jj) {
                std::uint32_t u = (std::uint32_t)rng.range(1000000);
                std::uint32_t ci = chnCi(nkCount + jj + 1ull);
                std::uint32_t mag = u ^ ci;
                w.u1(tmap[4]);
                w.u1(0);
                pushVarint(w, mag);
                chnMix(u);
            }
            const std::uint32_t ksd = (std::uint32_t)chn;
            for (int ch : chAll) w.u2((std::uint32_t)(ch + 1));
            std::vector<std::string> ebs(p.code.size());
            std::vector<std::uint8_t> lens(p.code.size(), 0);
            std::vector<std::pair<int, std::uint32_t>> jts;
            double tl0 = stick();
            for (size_t ii = 0; ii < p.code.size(); ++ii) {
                const VInstr& in = p.code[ii];
                int op = in.op;
                int opid = out.opId[op];
                VLayout lay = (VLayout)layOpid[opid];
                PcMask pm = pcMaskOf(key, key2, (int)ii + 1, bLayer, isJumpOp(op), isaB != 0);
                std::string eb;
                int ob = p2[opid];
                if (bLayer) {
                    const int mo = (1 + preK) % 3;
                    if (mo == 1) ob = p2b[(size_t)ob];
                    else if (mo == 2) ob = p2c[(size_t)ob];
                }
                for (int t3 = 0; t3 < 3; ++t3) {
                    const int stg = PERM[ord2][t3];
                    const std::vector<int>& pp = stg == 0 ? p2d : (stg == 1 ? p2e : p2f);
                    ob = pp[(size_t)ob];
                }
                ob = (int)(((std::uint64_t)ob * afA + afB) % 251u);
                ob = (int)(((std::uint32_t)ob + pm.saltOp) % 251u);
                eb.push_back((char)(std::uint8_t)ob);
                std::int64_t delta = in.jump && in.target >= 0
                    ? (std::int64_t)in.target - ((std::int64_t)ii + 1) : 0;
                std::uint32_t kv = (op == VOP_CLOSURE)
                    ? (std::uint32_t)in.k : (std::uint32_t)remapK(in.k);
                if (op != VOP_CLOSURE) {
                    std::uint32_t kvm16 = mixIdx(key, (std::uint64_t)((int)ii + 1) * 131ull +
                                                 (std::uint64_t)opid) % 65536ull;
                    kv ^= kvm16;
                }
                std::uint32_t bv = (op == VOP_GETGF || op == VOP_GCALL ||
                                    op == VOP_GTAIL || op == VOP_TGET2 ||
                                    op == VOP_KARITH || op == VOP_TSETK ||
                                    op == VOP_TGETC || op == VOP_TADDK)
                    ? (std::uint32_t)remapK(in.b) : (std::uint32_t)in.b;
                auto kmasked = [&](std::uint32_t vv) -> std::uint32_t {
                    return (vv ^ km) & 0xFFFFu;
                };
                auto pb1e = [&](std::uint32_t v) {
                    if (isaB) {
                        eb.push_back((char)(std::uint8_t)(v & 0xFFu));
                        eb.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
                    } else {
                        eb.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
                        eb.push_back((char)(std::uint8_t)(v & 0xFFu));
                    }
                };
                auto ps24 = [&](std::uint32_t v) {
                    if (isaB) {
                        eb.push_back((char)(std::uint8_t)(v & 0xFFu));
                        eb.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
                        eb.push_back((char)(std::uint8_t)((v >> 16) & 0xFFu));
                    } else {
                        eb.push_back((char)(std::uint8_t)((v >> 16) & 0xFFu));
                        eb.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
                        eb.push_back((char)(std::uint8_t)(v & 0xFFu));
                    }
                };
                auto junk2 = [&]() {
                    eb.push_back((char)(std::uint8_t)rng.range(256));
                    eb.push_back((char)(std::uint8_t)rng.range(256));
                };
                auto junk3 = [&]() {
                    eb.push_back((char)(std::uint8_t)rng.range(256));
                    eb.push_back((char)(std::uint8_t)rng.range(256));
                    eb.push_back((char)(std::uint8_t)rng.range(256));
                };
                switch (lay) {
                    case VL_ABC4: eb.push_back((char)in.a); eb.push_back((char)in.b); eb.push_back((char)in.c); break;
                    case VL_BAC4: eb.push_back((char)in.b); eb.push_back((char)in.a); eb.push_back((char)in.c); break;
                    case VL_AB3: eb.push_back((char)in.a); eb.push_back((char)in.b); break;
                    case VL_BA3: eb.push_back((char)in.b); eb.push_back((char)in.a); break;
                    case VL_A2: eb.push_back((char)in.a); break;
                    case VL_AK3:
                        eb.push_back((char)in.a);
                        pb1e(kmasked(kv));
                        break;
                    case VL_KA3:
                        pb1e(kmasked(kv));
                        eb.push_back((char)in.a);
                        break;
                    case VL_S24:
                        eb.push_back((char)in.a);
                        if (isJumpOp(op)) {
                            junk3();
                        } else {
                            std::uint32_t m = loadMask(key, (int)ii + 1);
                            std::int64_t v = ((in.s + (std::int64_t)m) % kMask24 + kMask24) % kMask24;
                            ps24((std::uint32_t)v);
                        }
                        break;
                    case VL_ABK5: eb.push_back((char)in.a); eb.push_back((char)in.b); pb1e(kmasked(kv)); break;
                    case VL_KK6: eb.push_back((char)in.a); pb1e(kmasked(kv)); pb1e(kmasked(bv)); break;
                    case VL_S16C5:
                        eb.push_back((char)in.a);
                        eb.push_back((char)in.c);
                        if (isJumpOp(op)) {
                            junk2();
                        } else {
                            std::uint32_t m = jumpMask(key, (int)ii + 1, opid) % kMask16;
                            std::int64_t v = ((delta + (std::int64_t)m) % kMask16 + kMask16) % kMask16;
                            eb.push_back((char)(std::uint8_t)((v >> 8) & 0xFFu));
                            eb.push_back((char)(std::uint8_t)(v & 0xFFu));
                        }
                        break;
                    case VL_ABS24:
                        eb.push_back((char)in.a);
                        eb.push_back((char)in.b);
                        junk3();
                        break;
                    case VL_SCA7:
                        eb.push_back((char)in.a);
                        eb.push_back((char)in.b);
                        eb.push_back((char)in.c);
                        eb.push_back((char)(std::uint8_t)in.s);
                        pb1e(kmasked(kv));
                        break;
                    case VL_SCK7:
                        eb.push_back((char)in.a);
                        pb1e(kmasked(bv));
                        eb.push_back((char)in.c);
                        eb.push_back((char)(std::uint8_t)in.s);
                        pb1e(kmasked(kv));
                        break;
                    case VL_ABSK7:
                        eb.push_back((char)in.a);
                        junk3();
                        pb1e(kmasked(kv));
                        break;
                    case VL_ABS6:
                        eb.push_back((char)in.a);
                        eb.push_back((char)in.b);
                        {
                            std::uint32_t m = loadMask(key, (int)ii + 1);
                            std::int64_t v = ((in.s + (std::int64_t)m) % kMask24 + kMask24) % kMask24;
                            ps24((std::uint32_t)v);
                        }
                        break;
                    case VL_AKK6:
                        eb.push_back((char)in.a);
                        pb1e(kmasked(kv));
                        pb1e(kmasked((std::uint32_t)remapK(in.b)));
                        break;
                    default: break;
                }
                int opPos = 0;
                const bool isaBOn = isaB != 0 && eb.size() >= 2;
                {
                    const int cap = 8 - (int)eb.size();
                    int nghost = 0;
                    if (cap >= 1 && rng.chance(0.45)) nghost = 1;
                    if (nghost == 1 && cap >= 2 && rng.chance(0.25)) nghost = 2;
                    for (int qg = 0; qg < nghost; ++qg)
                        eb.push_back((char)(std::uint8_t)rng.range(256));
                    const int pn = (int)eb.size() - 1;
                    if (pn >= 2 && pn <= 9 && !isaBOn) {

                        int pp[10];
                        for (int m = 1; m <= pn; ++m) pp[m] = m;
                        std::uint32_t st5 = pm.permSeed;
                        for (int m = pn; m >= 2; --m) {
                            st5 = lehmer(st5);
                            int j5 = 1 + (int)(st5 % (std::uint32_t)m);
                            int tmpPP = pp[m]; pp[m] = pp[j5]; pp[j5] = tmpPP;
                        }

                        char tb2[16];
                        const int ebn = (int)eb.size();
                        for (int m = 0; m < ebn; ++m) tb2[m] = eb[(size_t)m];
                        for (int m = 1; m <= pn; ++m)
                            eb[(size_t)pp[m]] = tb2[m];
                        if (dbgPp && pid == 0) {
                            static std::ofstream pf2("/tmp/ppdbg.txt", std::ios::trunc);
                            pf2 << (int)ii + 1 << " key " << key << " pseed " << pm.permSeed
                                << " salt " << (unsigned)pm.saltOp
                                << " lay " << (int)lay << " a " << in.a
                                << " s " << in.s << " pp";
                            for (int m = 1; m <= pn; ++m) pf2 << " " << pp[(size_t)m];
                            pf2 << " ebpre";
                            for (int z = 0; z < ebn; ++z)
                                pf2 << " " << (unsigned)(std::uint8_t)tb2[z];
                            pf2 << " ebfin";
                            for (int z = 0; z < (int)eb.size(); ++z)
                                pf2 << " " << (unsigned)(std::uint8_t)eb[z];
                            pf2 << "\n";
                        }
                    }
                }
                if (isaBOn) {
                    const int ln2 = (int)eb.size();

                    int ol[10];
                    for (int m = 0; m < ln2; ++m) ol[m] = m;
                    std::uint32_t st6 = pm.permSeed2;
                    for (int m = ln2 - 1; m >= 1; --m) {
                        st6 = lehmer(st6);
                        int q6 = (int)(st6 % (std::uint32_t)(m + 1));
                        int tmpOL = ol[m]; ol[m] = ol[q6]; ol[q6] = tmpOL;
                    }
                    char tb3[16];
                    for (int m = 0; m < ln2; ++m) tb3[m] = eb[(size_t)m];
                    for (int m = 0; m < ln2; ++m)
                        eb[(size_t)ol[m]] = tb3[m];
                    opPos = ol[0];
                }
                if (isaBOn) {
                    for (int z = 0; z < (int)eb.size(); ++z) {
                        if (z == opPos) continue;
                        eb[(size_t)z] = (char)((std::uint8_t)eb[(size_t)z] ^ pm.a[(size_t)z]);
                        if (bLayer && z >= 1 && z <= 8)
                            eb[(size_t)z] = (char)((std::uint8_t)eb[(size_t)z] ^ pm.b[(size_t)z - 1]);
                    }
                    eb[(size_t)opPos] = (char)((std::uint8_t)eb[(size_t)opPos] ^ pm.a[0u]);
                } else {
                    if (bLayer) {
                        for (size_t z = 1; z < eb.size() && z <= 8; ++z)
                            eb[z] = (char)((std::uint8_t)eb[z] ^ pm.b[z - 1]);
                    }
                    for (size_t z = 0; z < eb.size(); ++z)
                        eb[z] = (char)((std::uint8_t)eb[z] ^ pm.a[z]);
                }
                std::uint32_t acc = pck[pid];
                for (size_t z = 0; z < eb.size(); ++z)
                    acc = (std::uint32_t)(((std::uint64_t)acc * (std::uint64_t)g_bc.cmM +
                        (std::uint64_t)(std::uint8_t)eb[z]) & 0xFFFFFFFFull);
                pck[pid] = acc;
                if (veil0 != 0u) {
                    std::uint64_t wbase = ((std::uint64_t)veil0 +
                        (std::uint64_t)ksd * (std::uint64_t)g_bc.mc) % kMod31;
                    if (wbase < 1ull) wbase += 2147483646ull;
                    std::uint32_t w0 = mixIdx(wbase, (std::uint64_t)((int)ii + 1));
                    std::uint32_t wa = lehmer(w0);
                    std::uint32_t wb = lehmer(wa);
                    if (dbgVeil && pid == 0 && ii < 6) {
                        std::fprintf(stderr, "VEIL pid%d ii%zu op%d opid%d len%zu key%u veil0%u w0%u wa%u wb%u ebpre",
                                     pid, ii, (int)op, (int)opid, eb.size(), key, veil0, w0, wa, wb);
                        for (size_t z = 0; z < eb.size(); ++z)
                            std::fprintf(stderr, " %u", (unsigned)(std::uint8_t)eb[z]);
                    }
                    std::uint8_t vt[8];
                    vt[0] = (std::uint8_t)(wa & 0xFFu);
                    vt[1] = (std::uint8_t)((wa >> 8) & 0xFFu);
                    vt[2] = (std::uint8_t)((wa >> 16) & 0xFFu);
                    vt[3] = (std::uint8_t)((wa >> 24) & 0xFFu);
                    vt[4] = (std::uint8_t)(wb & 0xFFu);
                    vt[5] = (std::uint8_t)((wb >> 8) & 0xFFu);
                    vt[6] = (std::uint8_t)((wb >> 16) & 0xFFu);
                    vt[7] = (std::uint8_t)((wb >> 24) & 0xFFu);
                    if (isaBOn) {
                        for (size_t z = 0; z < eb.size(); ++z)
                            if ((int)z != opPos)
                                eb[(size_t)z] = (char)((std::uint8_t)eb[(size_t)z] ^ vt[z]);
                        eb[(size_t)opPos] = (char)((std::uint8_t)eb[(size_t)opPos] ^ vt[(size_t)opPos]);
                    } else {
                        for (size_t z = 0; z < eb.size(); ++z)
                            eb[(size_t)z] = (char)((std::uint8_t)eb[(size_t)z] ^ vt[z]);
                    }
                }
                if (dbgIs && isaB) {
                    std::fprintf(stderr, "SRV|pid=%d|pc=%d|ln=%d|opPos=%d|eb=", pid, (int)ii + 1, (int)eb.size(), opPos);
                    for (size_t z = 0; z < eb.size(); ++z) std::fprintf(stderr, "%02x", (unsigned)(std::uint8_t)eb[z]);
                    std::fprintf(stderr, "|opid=%d\n", opid);
                }
                lens[ii] = (std::uint8_t)eb.size();
                ebs[ii] = std::move(eb);
                if (isJumpOp(op)) {
                    std::uint32_t v = (std::uint32_t)(((delta + (std::int64_t)jumpMask(key, (int)ii + 1, opid) +
                        (std::int64_t)jumpDyn(key, (int)ii + 1, opid)) % kMask24 + kMask24) % kMask24);
                    {
                        std::uint8_t j0 = (std::uint8_t)((v >> 16) & 0xFFu) ^ pm.j[0];
                        std::uint8_t j1 = (std::uint8_t)((v >> 8) & 0xFFu) ^ pm.j[1];
                        std::uint8_t j2 = (std::uint8_t)(v & 0xFFu) ^ pm.j[2];
                        v = ((std::uint32_t)j0 << 16) | ((std::uint32_t)j1 << 8) | (std::uint32_t)j2;
                    }
                    jts.push_back({(int)ii + 1, v});
                }
            }
            const size_t niN = p.code.size();
            std::uint32_t ost = mixIdx(key, (std::uint64_t)g_bc.ikS);
            std::vector<int> ord(niN);
            for (size_t k = 0; k < niN; ++k) ord[k] = (int)k;
            for (size_t k = niN; k >= 2; --k) {
                ost = lehmer(ost);
                size_t j = (size_t)(ost % (std::uint32_t)k);
                std::swap(ord[k - 1], ord[j]);
            }
            std::string ib;
            ib.reserve(p.code.size() * 10);
            for (size_t k = 0; k < niN; ++k) {
                ib += ebs[(size_t)ord[k]];
            }
            for (size_t k = 0; k < niN; k += 2) {
                unsigned lo = lens[k];
                unsigned hi = (k + 1 < niN) ? lens[k + 1] : 0u;
                w.u1((std::uint32_t)(lo | (hi << 4)));
            }
            w.raw(ib);
            {
                const int dnjt = (int)rng.range(4);
                if (dnjt > 0 && niN > 0) {
                    std::vector<char> jpc(niN + 1, 0);
                    for (const auto& jtE : jts)
                        if (jtE.first >= 1 && jtE.first <= (int)niN)
                            jpc[(size_t)jtE.first] = 1;
                    for (int qd3 = 0; qd3 < dnjt; ++qd3) {
                        int rj = 1 + (int)rng.range((std::uint64_t)niN);
                        if (jpc[(size_t)rj]) continue;
                        jpc[(size_t)rj] = 1;
                        std::uint32_t dv2 = (std::uint32_t)rng.range(kMask24);
                        {
                            PcMask pj3 = pcMaskOf(key, key2, rj, bLayer, true);
                            std::uint8_t d0 = (std::uint8_t)((dv2 >> 16) & 0xFFu) ^ pj3.j[0];
                            std::uint8_t d1 = (std::uint8_t)((dv2 >> 8) & 0xFFu) ^ pj3.j[1];
                            std::uint8_t d2 = (std::uint8_t)(dv2 & 0xFFu) ^ pj3.j[2];
                            dv2 = ((std::uint32_t)d0 << 16) | ((std::uint32_t)d1 << 8) |
                                  (std::uint32_t)d2;
                        }
                        jts.push_back({rj, dv2});
                    }
                }
            }
            w.u2((std::uint32_t)jts.size());
            for (const auto& jt : jts) {
                w.u2((std::uint32_t)jt.first);
                w.u3(jt.second);
            }
            for (const auto& f : p.flat) {
                w.u4((std::uint32_t)f.first);
                w.u4((std::uint32_t)(f.second + 1));
            }
            tLoop += stick() - tl0;
            {
                double tp0 = stick();
                payload = azPack(w.b);
                tAz += stick() - tp0;
                double te0 = stick();
                encryptStreamInPlace(payload, key);
                tEnc += stick() - te0;
                double ts0 = stick();
                sboxApplyInPlace(payload, sbox);
                tSbox += stick() - ts0;
            }
            if (dbgOp && pid == 0) {
                static std::ofstream od("/tmp/opdbg.txt", std::ios::trunc);
                for (size_t kk2 = 0; kk2 < p.ks.size(); ++kk2)
                    od << "K" << (kk2 + 1) << " t " << (int)p.ks[kk2].t
                       << " n " << std::setprecision(17) << p.ks[kk2].n
                       << " sign " << (p.ks[kk2].t == VConst::NUM && std::signbit(p.ks[kk2].n) ? 1 : 0)
                       << " s " << p.ks[kk2].s << "\n";
                for (size_t ii2 = 0; ii2 < p.code.size(); ++ii2) {
                    int opid2 = out.opId[p.code[ii2].op];
                    od << (ii2 + 1) << " opid " << opid2 << " t " << p2[opid2]
                       << " lay " << layOpid[opid2] << " a " << p.code[ii2].a
                       << " b " << p.code[ii2].b << " c " << p.code[ii2].c
                       << " s " << p.code[ii2].s << " k " << p.code[ii2].k
                       << " canon " << canonOf[(size_t)opid2] << "\n";
                }
            }
        } else if (sl.kind == 1) {
            poolPos = pos;
            std::uint32_t poolKey = (poolBaseV + poolDelta) % kMod31;
            if (poolKey < 1u) poolKey += 2147483646u;
            poolKey = (std::uint32_t)(((std::uint64_t)poolKey + pv) % kMod31);
            if (poolKey < 1u) poolKey += 2147483646u;
            out.poolKey = poolBaseV;
            std::vector<std::string> encs(poolFrag.size());
            for (size_t gi = 0; gi < poolFrag.size(); ++gi)
                encs[(size_t)gi] = encryptStr(poolFrag[(size_t)gi], strKeyOf(poolKey, (int)gi + 1));
            W sp;
            sp.u2((std::uint32_t)poolFrag.size());
            for (size_t gi = 0; gi < poolFrag.size(); ++gi)
                sp.u2((std::uint32_t)encs[(size_t)gi].size() |
                      (fragFlag[(size_t)gi] ? 0x8000u : 0u));
            for (size_t gi = 0; gi < poolFrag.size(); ++gi)
                sp.raw(encs[(size_t)gi]);
            payload = sp.b;
            for (size_t pi = 0; pi < payload.size(); ++pi) {
                KStream ks = kStreamOf(poolKey, (int)pi + 1);
                payload[(size_t)pi] = (char)((std::uint8_t)payload[(size_t)pi] ^
                                             (std::uint8_t)ks.k[(size_t)(pi % 5)]);
            }
            sboxApplyInPlace(payload, sbox);
        } else if (sl.kind == 3) {
            const int fpos = pos;
            std::uint32_t fkey = protoKeyOf(out.buildSeed, 8000 + fpos * 173);
            fkey = (std::uint32_t)(((std::uint64_t)fkey + pv) % kMod31);
            if (fkey < 1u) fkey += 2147483646u;
            const int fcnt = 2 + (int)rng.range(4);
            W fp;
            fp.u2((std::uint32_t)fcnt);
            std::vector<std::string> fencs((size_t)fcnt);
            for (int gi = 0; gi < fcnt; ++gi) {
                int flen = 6 + (int)rng.range(28);
                std::string fe;
                for (int zb = 0; zb < flen; ++zb)
                    fe.push_back((char)(33 + (int)rng.range(90)));
                fencs[(size_t)gi] = fe;
            }
            for (int gi = 0; gi < fcnt; ++gi)
                fp.u2((std::uint32_t)fencs[(size_t)gi].size());
            for (int gi = 0; gi < fcnt; ++gi)
                fp.raw(fencs[(size_t)gi]);
            payload = fp.b;
            for (size_t pi = 0; pi < payload.size(); ++pi) {
                KStream fks = kStreamOf(fkey, (int)pi + 1);
                payload[(size_t)pi] = (char)((std::uint8_t)payload[(size_t)pi] ^
                                             (std::uint8_t)fks.k[(size_t)(pi % 5)]);
            }
            sboxApplyInPlace(payload, sbox);
        } else {
            const int dpos = pos;
            std::uint32_t dkey = protoKeyOf(out.buildSeed, 9000 + pos * 131);
            dkey = (std::uint32_t)(((std::uint64_t)dkey + kd[(size_t)(dpos % (int)nprotos)] + pv) % kMod31);
            if (dkey < 1u) dkey += 2147483646u;
            std::vector<int> dp2(VOP_COUNT + 1, 0);
            protoShuffle(dp2, dkey);
            std::uint32_t dkey2 = 0;
            std::vector<int> dp2b(VOP_COUNT + 1, 0);
            if (bLayer) {
                dkey2 = key2Of(dkey, out.blobSalt);
                protoShuffle(dp2b, dkey2);
            }
            const std::uint32_t dafs0 = (dkey + g_bc.sc) % kMod31;
            const std::uint32_t dafA = 3u + lehmer(dafs0) % 247u;
            const std::uint32_t dafB = lehmer(dafs0 + g_bc.sd) % 251u;
            W w;
            w.u2((std::uint32_t)rng.range(4));
            w.u1(rng.chance(0.3) ? 1u : 0u);
            w.u1((std::uint32_t)rng.range(8));
            w.u2((std::uint32_t)rng.range(3));
            w.u2((std::uint32_t)(8 + rng.range(14)));
            w.u2((std::uint32_t)(2 + rng.range(6)));
            w.u2((std::uint32_t)rng.range(3));
            const int dni = 8 + (int)rng.range(30);
            w.u2((std::uint32_t)dni);
            w.u2((std::uint32_t)rng.range(4));
            for (int iu = 0; iu < (int)rng.range(3); ++iu) {
                w.u1((std::uint32_t)rng.range(2));
                w.u2((std::uint32_t)rng.range(40));
            }
            for (int ik = 0; ik < 2 + (int)rng.range(6); ++ik) {
                if (rng.chance(0.4) && !pool.empty()) {
                    w.u1(5);
                    w.u2((std::uint32_t)(1 + rng.range((std::uint64_t)pool.size())));
                } else {
                    w.u1(4);
                    w.u1((std::uint32_t)rng.range(2));
                    pushVarint(w, (std::uint64_t)rng.range(1000000));
                }
            }
            std::vector<int> dch;
            for (int icc = 0; icc < (int)rng.range(3); ++icc) {
                int chv = (int)rng.range((std::uint64_t)(nprotos + 2));
                dch.push_back(chv);
                w.u2((std::uint32_t)(chv + 1));
            }
            std::string dib;
            const std::uint32_t dkmv = kMaskOf(dkey, 251);
            for (int ii = 0; ii < dni; ++ii) {
                int dop;
                if (!dch.empty() && rng.chance(0.2)) dop = VOP_CLOSURE;
                else dop = (int)rng.range((std::uint64_t)VOP_DECOY11 + 1);
                int dopid = out.opId[dop];
                int dob = dp2[(size_t)dopid];
                if (bLayer) dob = dp2b[(size_t)dob];
                dob = (int)(((std::uint64_t)dob * dafA + dafB) % 251u);
                VLayout dlay = (VLayout)out.opLayout[dop];
                int dlen = layoutSize(dlay);
                PcMask dpm = pcMaskOf(dkey, dkey2, ii + 1, bLayer);
                dob = (int)(((std::uint32_t)dob + dpm.saltOp) % 251u);
                int da = 1 + (int)rng.range(20);
                int dbb = (int)rng.range(20);
                int dcc = (int)rng.range(20);
                std::uint32_t dkv;
                if (dop == VOP_CLOSURE && !dch.empty())
                    dkv = (std::uint32_t)dch[(size_t)rng.range(dch.size())];
                else if (rng.chance(0.6) && !pool.empty())
                    dkv = 1 + (std::uint32_t)rng.range((std::uint64_t)pool.size());
                else
                    dkv = (std::uint32_t)rng.range(100000);
                auto dkM = [&](std::uint32_t vv) -> std::uint32_t {
                    return (vv ^ dkmv) & 0xFFFFu;
                };
                std::string deb;
                deb.push_back((char)(std::uint8_t)dob);
                auto dpb1 = [&](std::uint32_t vv) {
                    deb.push_back((char)(std::uint8_t)((vv >> 8) & 0xFFu));
                    deb.push_back((char)(std::uint8_t)(vv & 0xFFu));
                };
                auto djunk = [&](int n) {
                    for (int qj = 0; qj < n; ++qj)
                        deb.push_back((char)(std::uint8_t)rng.range(256));
                };
                switch (dlay) {
                    case VL_ABC4: deb.push_back((char)da); deb.push_back((char)dbb); deb.push_back((char)dcc); break;
                    case VL_BAC4: deb.push_back((char)dbb); deb.push_back((char)da); deb.push_back((char)dcc); break;
                    case VL_AB3: deb.push_back((char)da); deb.push_back((char)dbb); break;
                    case VL_BA3: deb.push_back((char)dbb); deb.push_back((char)da); break;
                    case VL_A2: deb.push_back((char)da); break;
                    case VL_AK3: deb.push_back((char)da); dpb1(dkM(dkv)); break;
                    case VL_KA3: dpb1(dkM(dkv)); deb.push_back((char)da); break;
                    case VL_S24:
                        deb.push_back((char)da);
                if (isJumpOp(dop)) djunk(3);
                        else {
                            std::uint32_t m2x = loadMask(dkey, ii + 1);
                            std::int64_t vv2 = ((rng.range(2000) + (std::int64_t)m2x) % kMask24 + kMask24) % kMask24;
                            deb.push_back((char)(std::uint8_t)((vv2 >> 16) & 0xFFu));
                            deb.push_back((char)(std::uint8_t)((vv2 >> 8) & 0xFFu));
                            deb.push_back((char)(std::uint8_t)(vv2 & 0xFFu));
                        }
                        break;
                    case VL_ABK5: deb.push_back((char)da); deb.push_back((char)dbb); dpb1(dkM(dkv)); break;
                    case VL_KK6: deb.push_back((char)da); dpb1(dkM(dkv)); dpb1(dkM(dbb)); break;
                    case VL_S16C5:
                        deb.push_back((char)da);
                        deb.push_back((char)dcc);
                        if (isJumpOp(dop)) djunk(2);
                        else {
                            std::uint32_t m2x = jumpMask(dkey, ii + 1, dopid) % kMask16;
                            std::int64_t vv2 = (((std::int64_t)rng.range(600) + (std::int64_t)m2x) % kMask16 + kMask16) % kMask16;
                            deb.push_back((char)(std::uint8_t)((vv2 >> 8) & 0xFFu));
                            deb.push_back((char)(std::uint8_t)(vv2 & 0xFFu));
                        }
                        break;
                    case VL_ABS24: deb.push_back((char)da); deb.push_back((char)dbb); djunk(3); break;
                    case VL_SCA7: deb.push_back((char)da); deb.push_back((char)dbb); deb.push_back((char)dcc); deb.push_back((char)(std::uint8_t)rng.range(256)); dpb1(dkM(dkv)); break;
                    case VL_SCK7: deb.push_back((char)da); dpb1(dkM(dbb)); deb.push_back((char)dcc); deb.push_back((char)(std::uint8_t)rng.range(256)); dpb1(dkM(dkv)); break;
                    case VL_ABSK7: deb.push_back((char)da); djunk(3); dpb1(dkM(dkv)); break;
                    case VL_ABS6: {
                        deb.push_back((char)da);
                        deb.push_back((char)dbb);
                        std::uint32_t m2x = loadMask(dkey, ii + 1);
                        std::int64_t vv2 = ((rng.range(2000) + (std::int64_t)m2x) % kMask24 + kMask24) % kMask24;
                        deb.push_back((char)(std::uint8_t)((vv2 >> 16) & 0xFFu));
                        deb.push_back((char)(std::uint8_t)((vv2 >> 8) & 0xFFu));
                        deb.push_back((char)(std::uint8_t)(vv2 & 0xFFu));
                        break;
                    }
                    case VL_AKK6: deb.push_back((char)da); dpb1(dkM(dkv)); dpb1(dkM(dbb)); break;
                    default: djunk(dlen - 1); break;
                }
                while ((int)deb.size() < dlen) deb.push_back((char)(std::uint8_t)rng.range(256));
                if (bLayer)
                    for (size_t zb = 1; zb < deb.size() && zb <= 8; ++zb)
                        deb[(size_t)zb] = (char)((std::uint8_t)deb[(size_t)zb] ^ dpm.b[zb - 1]);
                for (size_t zb = 0; zb < deb.size(); ++zb)
                    deb[(size_t)zb] = (char)((std::uint8_t)deb[(size_t)zb] ^ dpm.a[zb]);
                dib += deb;
            }
            w.raw(dib);
            for (int q = 0; q < 8; ++q) w.u1(0);
            const int dnj = dni / 4 + (int)rng.range(3);
            w.u2((std::uint32_t)dnj);
            for (int qd = 0; qd < dnj; ++qd) {
                int dji = 1 + (int)rng.range((std::uint64_t)dni);
                std::uint32_t dv = (std::uint32_t)((((std::int64_t)rng.range(kMask24) - (std::int64_t)(kMask24 / 2) +
                    (std::int64_t)jumpMask(dkey, dji, 0) + (std::int64_t)jumpDyn(dkey, dji, 0)) % kMask24 + kMask24) % kMask24);
                {
                    PcMask pmj = pcMaskOf(dkey, dkey2, dji, bLayer, true);
                    std::uint8_t j0 = (std::uint8_t)((dv >> 16) & 0xFFu) ^ pmj.j[0];
                    std::uint8_t j1 = (std::uint8_t)((dv >> 8) & 0xFFu) ^ pmj.j[1];
                    std::uint8_t j2 = (std::uint8_t)(dv & 0xFFu) ^ pmj.j[2];
                    dv = ((std::uint32_t)j0 << 16) | ((std::uint32_t)j1 << 8) | (std::uint32_t)j2;
                }
                w.u2((std::uint32_t)dji);
                w.u3(dv);
            }
            for (int qf = 0; qf < (int)rng.range(4); ++qf) {
                w.u4((std::uint32_t)rng.range(1000000));
                w.u4((std::uint32_t)(1 + rng.range((std::uint64_t)dni)));
            }
            {
                double tp0 = stick();
                payload = azPack(w.b);
                tAz += stick() - tp0;
                double te0 = stick();
                encryptStreamInPlace(payload, dkey);
                tEnc += stick() - te0;
                double ts0 = stick();
                sboxApplyInPlace(payload, sbox);
                tSbox += stick() - ts0;
            }
        }
        std::uint32_t salt = sectionSalt(out.blobSalt, pos);
        cs[(size_t)pos] = checksum32(payload, salt);
        secPay[(size_t)pos] = payload;
    }

    W vb;
    vb.u2((std::uint32_t)nprotos);
    for (size_t i = 0; i < nprotos; ++i) vb.u4(kd[i]);
    vb.u4(poolDelta);
    vb.u2((std::uint32_t)poolPos);
    for (size_t i = 0; i < nprotos; ++i) vb.u2((std::uint32_t)posOfProto[(size_t)i]);
    for (size_t i = 0; i < nprotos; ++i) {
        pck[i] = xor32(pck[i], pck[i] >> 11);
        pck[i] = (std::uint32_t)(((std::uint64_t)pck[i] * g_bc.cmM2 + g_bc.ivM2) & 0xFFFFFFFFull);
    }
    for (size_t i = 0; i < nprotos; ++i) vb.u4(pck[i]);
    for (size_t i = 0; i < nprotos; ++i) vb.u1((std::uint32_t)keArr[i]);
    std::string vbEnc;
    {
        std::uint32_t vk = vaultKeyOf(out.blobSalt, out.buildSeed);
        std::uint32_t vk2 = (std::uint32_t)(((std::uint64_t)vk +
            cs[(size_t)(totalMiddle + 1)]) % kMod31);
        if (vk2 < 1u) vk2 += 2147483646u;
        vbEnc = sboxApply(encryptStream(vb.b, vk2), sbox);
        cs[(size_t)(totalMiddle + 2)] =
            checksum32(vbEnc, sectionSalt(out.blobSalt, totalMiddle + 2));
    }

    for (int pos = 2; pos <= totalMiddle + 1; ++pos) {
        const std::string& payload = secPay[(size_t)pos];
        W fh;
        fh.u4((std::uint32_t)payload.size());
        fh.u4(cs[(size_t)pos] ^ cs[(size_t)pos + 1]);
        for (size_t q = 0; q < fh.b.size(); ++q) {
            hdrSt = lehmer(hdrSt);
            fh.b[(size_t)q] = (char)((std::uint8_t)fh.b[(size_t)q] ^ (std::uint8_t)(hdrSt & 0xFFu));
        }
        afterMeta.append(fh.b);
        afterMeta.append(payload);
    }
    {
        W fh;
        fh.u4((std::uint32_t)vbEnc.size());
        fh.u4(cs[(size_t)(totalMiddle + 2)] ^ out.blobSalt);
        for (size_t q = 0; q < fh.b.size(); ++q) {
            hdrSt = lehmer(hdrSt);
            fh.b[(size_t)q] = (char)((std::uint8_t)fh.b[(size_t)q] ^ (std::uint8_t)(hdrSt & 0xFFu));
        }
        afterMeta.append(fh.b);
        afterMeta.append(vbEnc);
    }

    W meta;
    meta.u4((std::uint32_t)(totalMiddle + 2));
    meta.u4((std::uint32_t)ir.entry);
    meta.u4((std::uint32_t)ir.protos.size());
    meta.u4((std::uint32_t)out.flush);
    meta.u4(checksum32(afterMeta, out.blobSalt));
    {
        std::string metaEnc =
            sboxApply(encryptStream(meta.b, vaultKeyOf(out.blobSalt, out.buildSeed)), sbox);
        std::uint32_t metaCk = checksum32(metaEnc, sectionSalt(out.blobSalt, 1));
        {
            std::string fv;
            {
                W fh;
                fh.u4((std::uint32_t)metaEnc.size());
                fh.u4(metaCk ^ cs[(size_t)2]);
                fv.append(fh.b);
            }
            fv.append(metaEnc);
            for (int pos = 2; pos <= totalMiddle + 1; ++pos) {
                W fh;
                fh.u4((std::uint32_t)secPay[(size_t)pos].size());
                fh.u4(cs[(size_t)pos] ^ cs[(size_t)pos + 1]);
                fv.append(fh.b);
                fv.append(secPay[(size_t)pos]);
            }
            {
                W fh;
                fh.u4((std::uint32_t)vbEnc.size());
                fh.u4(cs[(size_t)(totalMiddle + 2)] ^ out.blobSalt);
                fv.append(fh.b);
                fv.append(vbEnc);
            }
            out.foldView = fv;
        }
        W fh;
        fh.u4((std::uint32_t)metaEnc.size());
        fh.u4(metaCk ^ cs[(size_t)2]);
        for (size_t q = 0; q < fh.b.size(); ++q)
            fh.b[(size_t)q] = (char)((std::uint8_t)fh.b[(size_t)q] ^ metaHs[q]);
        out.blob = fh.b + metaEnc + afterMeta;
    }

    out.digest = checksum32(afterMeta, out.blobSalt);
    if (std::getenv("EXF_NO_SIGN") == nullptr) {
        out.sig.resize(64);
        ed25519::sign(reinterpret_cast<const std::uint8_t*>(out.blob.data()),
                      out.blob.size(), reinterpret_cast<std::uint8_t*>(&out.sig[0]));
    }
    if (std::getenv("EXF_NO_SIGN") == nullptr) {
        out.sig.resize(64);
        ed25519::sign(reinterpret_cast<const std::uint8_t*>(out.blob.data()),
                      out.blob.size(), reinterpret_cast<std::uint8_t*>(&out.sig[0]));
    }
    out.stringsIdx = poolPos;

    if (kvm) {
        Rng krng(seed ^ 0x6C13C0DEULL);
        const int kNop = 30;
        out.kOpIds.assign(kNop, 0);
        {
            std::vector<int> kp(kNop);
            for (int i = 0; i < kNop; ++i) kp[(size_t)i] = i + 1;
            for (int i = kNop - 1; i > 0; --i) {
                int j = (int)krng.range((std::uint64_t)(i + 1));
                std::swap(kp[(size_t)i], kp[(size_t)j]);
            }
            for (int i = 0; i < kNop; ++i) out.kOpIds[(size_t)i] = kp[(size_t)i];
        }
        out.kLay = (int)krng.range(3);
        out.kSlot = (int)krng.range(2);
        out.kW = 5 + (int)krng.range(3);
        out.kWG = 5 + (int)krng.range(3);

        enum { K_LDI, K_LDK, K_LG, K_MOV, K_ADD, K_SUB, K_MUL, K_MOD, K_ADDC,
               K_MULC, K_JMP, K_JLT, K_JGE, K_JEQ, K_ST, K_LDS, K_BOOT,
               K_HALT, K_DCY0, K_DCY1, K_XOR, K_OR, K_AND, K_SHL, K_SHR,
               K_JNE, K_NEG, K_XCHG, K_LD2, K_ST2, K_KCOUNT };
        auto isKJump = [](int op) {
            return op == K_JMP || op == K_JLT || op == K_JGE || op == K_JEQ ||
                   op == K_JNE;
        };
        struct KIns {
            int op = 0;
            int a = 0;
            int b = 0;
            int c = 0;
            int tgt = -1;
        };
        const std::uint32_t M = kMod31;
        const std::uint32_t M1 = kMod31 - 1;
        const int NREG = 8 + (int)krng.range(8);

        std::uint32_t Cg1 = 1 + (std::uint32_t)krng.range(M - 2);
        std::uint32_t vkExp = vaultKeyOf(out.blobSalt, out.buildSeed);
        std::uint32_t g1v = (vkExp + Cg1) % M;
        if (g1v < 1u) g1v += M1;
        out.kG1 = g1v;

        auto pickRegs = [&](Rng& r, int n) {
            std::vector<int> v(NREG);
            for (int i = 0; i < NREG; ++i) v[(size_t)i] = i + 1;
            for (int i = NREG - 1; i > 0; --i) {
                int j = (int)r.range((std::uint64_t)(i + 1));
                std::swap(v[(size_t)i], v[(size_t)j]);
            }
            v.resize((size_t)n);
            return v;
        };
        auto decoyTail = [&](std::vector<KIns>& p, Rng& r, std::vector<std::uint32_t>& cs) {
            std::vector<int> rg = pickRegs(r, 4);
            p.push_back({K_LDI, rg[0], (int)(1000 + r.range(60000)), 0, -1});
            p.push_back({K_LDI, rg[1], (int)(1 + r.range(900)), 0, -1});
            p.push_back({K_SUB, rg[0], rg[1], 0, -1});
            if (r.chance(0.5)) p.push_back({K_DCY0, rg[0], rg[1], 0, -1});
            else {
                cs.push_back(1 + (std::uint32_t)r.range(4294967294u));
                p.push_back({K_DCY1, rg[0], (int)cs.size(), 0, -1});
            }
            int dsel = (int)r.range(6);
            if (dsel == 0) p.push_back({K_XOR, rg[2], rg[3], 0, -1});
            else if (dsel == 1) p.push_back({K_OR, rg[2], rg[3], 0, -1});
            else if (dsel == 2) p.push_back({K_AND, rg[2], rg[3], 0, -1});
            else if (dsel == 3) p.push_back({K_SHL, rg[2], rg[3], 0, -1});
            else if (dsel == 4) { p.push_back({K_NEG, rg[2], 0, 0, -1}); p.push_back({K_XCHG, rg[2], rg[3], 0, -1}); }
            else p.push_back({K_SHR, rg[2], rg[3], 0, -1});
            p.push_back({K_XCHG, rg[0], rg[2], 0, -1});
            p.push_back({K_HALT, rg[0], 0, 0, -1});
        };

        std::vector<std::vector<KIns>> progs(5);
        std::vector<std::vector<std::uint32_t>> kcs(5);
        std::vector<int> order = {0, 1, 2, 3, 4};
        for (int i = 4; i > 0; --i) {
            int j = (int)krng.range((std::uint64_t)(i + 1));
            std::swap(order[(size_t)i], order[(size_t)j]);
        }
        out.kPA = (int)(std::find(order.begin(), order.end(), 0) - order.begin()) + 1;
        out.kPB = (int)(std::find(order.begin(), order.end(), 1) - order.begin()) + 1;
        out.kPC = (int)(std::find(order.begin(), order.end(), 2) - order.begin()) + 1;
        out.kPS = (int)(std::find(order.begin(), order.end(), 3) - order.begin()) + 1;
        out.kPK = (int)(std::find(order.begin(), order.end(), 4) - order.begin()) + 1;
        out.veilGate = 256 + (int)krng.range(768);
        out.nsf = totalMiddle + 2;

        for (int phase = 0; phase < 5; ++phase) {
            std::vector<KIns> p;
            std::vector<std::uint32_t>& cs = kcs[(size_t)phase];
            auto cidx = [&](std::uint32_t v) {
                for (size_t i = 0; i < cs.size(); ++i)
                    if (cs[i] == v) return (int)i + 1;
                cs.push_back(v);
                return (int)cs.size();
            };
            int cM = cidx(M);
            int cM1 = cidx(M1);
            std::vector<int> rg = pickRegs(krng, 8);
            int rV = rg[2], rT = rg[3], rO = rg[4];
            if (phase == 0) {
                int cVA = cidx(g_bc.va);
                int cVB = cidx(g_bc.vb2);
                int cVC = cidx(g_bc.vc);
                int cEF = cidx(envFoldOf());
                int c3 = cidx(3);
                int cCg1 = cidx(Cg1);
                int rK1 = 1, rK2 = 2, rO = 3, rV = 5, rA = 6, rG = 7;
                p.push_back({K_LG, rK1, 1, 0, -1});
                p.push_back({K_LG, rK2, 3, 0, -1});
                p.push_back({K_MOV, rV, rK1, 0, -1});
                p.push_back({K_MULC, rV, cVA, 0, -1});
                p.push_back({K_MOV, rA, rK2, 0, -1});
                p.push_back({K_MULC, rA, cVB, 0, -1});
                p.push_back({K_ADD, rV, rA, 0, -1});
                p.push_back({K_ADDC, rV, cVC, 0, -1});
                p.push_back({K_ADDC, rV, cEF, 0, -1});
                p.push_back({K_MOD, rV, cM, 0, -1});
                p.push_back({K_MOV, rA, rK2, 0, -1});
                p.push_back({K_MULC, rA, c3, 0, -1});
                p.push_back({K_ADD, rA, rK1, 0, -1});
                p.push_back({K_MOD, rA, cM, 0, -1});
                p.push_back({K_MOV, rG, rV, 0, -1});
                p.push_back({K_ADDC, rG, cCg1, 0, -1});
                p.push_back({K_MOD, rG, cM, 0, -1});
                p.push_back({K_LDI, rO, 1, 0, -1});
                int j1 = (int)p.size();
                p.push_back({K_JGE, rV, 0, rO, -1});
                p.push_back({K_ADDC, rV, cM1, 0, -1});
                int l1 = (int)p.size();
                int j2 = (int)p.size();
                p.push_back({K_JGE, rA, 0, rO, -1});
                p.push_back({K_ADDC, rA, cM1, 0, -1});
                int l2 = (int)p.size();
                int j3 = (int)p.size();
                p.push_back({K_JGE, rG, 0, rO, -1});
                p.push_back({K_ADDC, rG, cM1, 0, -1});
                int l3 = (int)p.size();
                p.push_back({K_BOOT, rV, 1 + 3 * 256, 0, -1});
                p[(size_t)j1].tgt = l1 + 1;
                p[(size_t)j2].tgt = l2 + 1;
                p[(size_t)j3].tgt = l3 + 1;
                decoyTail(p, krng, cs);
            } else if (phase == 1) {
                p.push_back({K_LDS, rV, 1, 0, -1});
                p.push_back({K_LDS, rT, 4, 0, -1});
                p.push_back({K_ADD, rV, rT, 0, -1});
                p.push_back({K_MOD, rV, cM, 0, -1});
                p.push_back({K_LDI, rO, 1, 0, -1});
                int j1 = (int)p.size();
                p.push_back({K_JGE, rV, 0, rO, -1});
                p.push_back({K_ADDC, rV, cM1, 0, -1});
                int l1 = (int)p.size();
                p.push_back({K_BOOT, rV, 5 + 256, 0, -1});
                p[(size_t)j1].tgt = l1 + 1;
                decoyTail(p, krng, cs);
            } else if (phase == 2) {
                std::uint32_t pkA = 1 + (std::uint32_t)krng.range(M - 2);
                std::uint32_t pkB = (out.poolKey + M - pkA) % M;
                if (pkB < 1u) pkB += M1;
                int cPKA = cidx(pkA);
                int cPKB = cidx(pkB);
                p.push_back({K_LDS, rV, 7, 0, -1});
                p.push_back({K_LD2, rV, cPKA, cPKB, -1});
                p.push_back({K_MOD, rV, cM, 0, -1});
                p.push_back({K_LDS, rT, 8, 0, -1});
                p.push_back({K_ADD, rV, rT, 0, -1});
                p.push_back({K_MOD, rV, cM, 0, -1});
                p.push_back({K_LDI, rO, 1, 0, -1});
                int j1 = (int)p.size();
                p.push_back({K_JGE, rV, 0, rO, -1});
                p.push_back({K_ADDC, rV, cM1, 0, -1});
                int l1 = (int)p.size();
                p.push_back({K_BOOT, rV, 9 + 256, 0, -1});
                p[(size_t)j1].tgt = l1 + 1;
                decoyTail(p, krng, cs);
            } else if (phase == 3) {
                std::uint32_t sC1 = 1 + (std::uint32_t)krng.range(46340);
                std::uint32_t sC2 = (std::uint32_t)krng.range(M - 1);
                int cC1 = cidx(sC1);
                std::uint32_t sC2a = 1 + (std::uint32_t)krng.range(M - 2);
                std::uint32_t sC2b = (sC2 + M - sC2a) % M;
                if (sC2b < 1u) sC2b += M1;
                int cC2a = cidx(sC2a);
                int cC2b = cidx(sC2b);
                p.push_back({K_LDS, rV, 12, 0, -1});
                p.push_back({K_MULC, rV, cC1, 0, -1});
                p.push_back({K_LD2, rV, cC2a, cC2b, -1});
                p.push_back({K_MOD, rV, cM, 0, -1});
                p.push_back({K_LDI, rO, 1, 0, -1});
                int j1 = (int)p.size();
                p.push_back({K_JGE, rV, 0, rO, -1});
                p.push_back({K_ADDC, rV, cM1, 0, -1});
                int l1 = (int)p.size();
                p.push_back({K_BOOT, rV, 11 + 256, 0, -1});
                p[(size_t)j1].tgt = l1 + 1;
                decoyTail(p, krng, cs);
            } else {
                int cA = cidx(g_bc.me);
                int cM6 = cidx(2147483646);
                int cM7 = cidx(kMod31);
                int cS4A = cidx(g_bc.s4a);
                int cS4B = cidx(g_bc.s4b);
                int cOne = cidx(1);
                int cM4 = cidx(g_bc.m4);
                int cSd = cidx(g_bc.sd);
                int cM1 = cidx(kMod31 - 1);
                int rW = rg[5], rSh = rg[6];
                p.push_back({K_LDI, rO, 1, 0, -1});
                p.push_back({K_LDI, rSh, 7, 0, -1});
                p.push_back({K_LDS, rT, 9, 0, -1});
                p.push_back({K_LDS, rV, 14, 0, -1});
                p.push_back({K_MULC, rV, cA, 0, -1});
                p.push_back({K_ADD, rV, rT, 0, -1});
                p.push_back({K_MOD, rV, cM6, 0, -1});
                p.push_back({K_MULC, rV, cM4, 0, -1});
                p.push_back({K_MOD, rV, cM7, 0, -1});
                p.push_back({K_MOV, rW, rV, 0, -1});
                p.push_back({K_SHR, rW, rSh, 0, -1});
                p.push_back({K_XOR, rV, rW, 0, -1});
                p.push_back({K_ADDC, rV, cSd, 0, -1});
                p.push_back({K_MOD, rV, cM7, 0, -1});
                {
                    int jg = (int)p.size();
                    p.push_back({K_JGE, rV, 0, rO, -1});
                    p.push_back({K_ADDC, rV, cM1, 0, -1});
                    p[(size_t)jg].tgt = (int)p.size() + 1;
                }
                p.push_back({K_MULC, rV, cS4A, 0, -1});
                p.push_back({K_ADDC, rV, cS4B, 0, -1});
                p.push_back({K_MOD, rV, cM6, 0, -1});
                p.push_back({K_MULC, rV, cM4, 0, -1});
                p.push_back({K_MOD, rV, cM7, 0, -1});
                p.push_back({K_MOV, rW, rV, 0, -1});
                p.push_back({K_SHR, rW, rSh, 0, -1});
                p.push_back({K_XOR, rV, rW, 0, -1});
                p.push_back({K_ADDC, rV, cSd, 0, -1});
                p.push_back({K_MOD, rV, cM7, 0, -1});
                {
                    int jg = (int)p.size();
                    p.push_back({K_JGE, rV, 0, rO, -1});
                    p.push_back({K_ADDC, rV, cM1, 0, -1});
                    p[(size_t)jg].tgt = (int)p.size() + 1;
                }
                p.push_back({K_MOV, rW, rV, 0, -1});
                p.push_back({K_SHR, rW, rSh, 0, -1});
                p.push_back({K_XOR, rV, rW, 0, -1});
                p.push_back({K_MOD, rV, cM6, 0, -1});
                p.push_back({K_ADDC, rV, cOne, 0, -1});
                p.push_back({K_BOOT, rV, 16 + 256, 0, -1});
                decoyTail(p, krng, cs);
            }
            for (KIns& q : p)
                if (q.tgt < 0 && !isKJump(q.op) && q.op != K_BOOT && q.op != K_HALT &&
                    q.op != K_LD2 && q.op != K_ST2)
                    q.c = (int)krng.range(256);
            progs[(size_t)phase] = p;
        }

        out.kLayG = (int)krng.range(3);
        auto serializeKInner = [&](W& inn, int lay, int wd) {
            int ord5[3][5] = {{1, 2, 3, 4, 5}, {5, 2, 3, 1, 4}, {3, 5, 1, 4, 2}};
            int ord6[3][6] = {{1, 2, 3, 4, 5, 0}, {5, 0, 2, 3, 1, 4}, {3, 5, 0, 1, 4, 2}};
            int ord7[3][7] = {{1, 2, 3, 4, 5, 0, 0}, {5, 0, 2, 3, 1, 4, 0}, {0, 3, 5, 0, 1, 4, 2}};
            const int* ordp = wd == 5 ? ord5[lay] : wd == 6 ? ord6[lay] : ord7[lay];
            inn.u2(5);
            inn.u1((std::uint32_t)wd);
            for (int oi = 0; oi < 5; ++oi) {
                const int phase = order[(size_t)oi];
                const std::vector<KIns>& p = progs[(size_t)phase];
                const std::vector<std::uint32_t>& cs = kcs[(size_t)phase];
                std::uint32_t pkey = 1 + (std::uint32_t)krng.range(M - 2);
                inn.u2((std::uint32_t)p.size());
                inn.u2((std::uint32_t)cs.size());
                inn.u1((std::uint32_t)NREG);
                inn.u4(pkey);
                for (std::uint32_t cv : cs) inn.u4(cv);
                for (size_t pc = 1; pc <= p.size(); ++pc) {
                    const KIns& q = p[(size_t)(pc - 1)];
                    int opid = out.kOpIds[(size_t)q.op];
                    int b16;
                    if (isKJump(q.op)) {
                        int delta = q.tgt - ((int)pc + 1);
                        std::uint32_t jm = kMaskOf(pkey, (int)pc);
                        b16 = (int)(((delta + (std::int64_t)jm) % kMask16 + kMask16) % kMask16);
                    } else {
                        b16 = q.b & 0xFFFFu;
                    }
                    int x8a = (out.kSlot == 0) ? q.a : q.c;
                    int x8c = (out.kSlot == 0) ? q.c : q.a;
                    unsigned char fv[6];
                    fv[0] = (unsigned char)krng.range(256);
                    fv[1] = (unsigned char)opid;
                    fv[2] = (unsigned char)x8a;
                    fv[3] = (unsigned char)((b16 >> 8) & 0xFFu);
                    fv[4] = (unsigned char)(b16 & 0xFFu);
                    fv[5] = (unsigned char)x8c;
                    unsigned char f[7];
                    for (int z = 0; z < wd; ++z) f[z] = fv[ordp[z]];
                    KStream ks5 = kStreamOf(pkey, (int)pc);
                    for (int z = 0; z < wd; ++z) f[z] = (unsigned char)(f[z] ^ ks5.k[z]);
                    for (int z = 0; z < wd; ++z) inn.u1(f[z]);
                }
            }
        };
        W inner;
        double tk0 = stick();
        serializeKInner(inner, out.kLay, out.kW);
        W innerG;
        serializeKInner(innerG, out.kLayG, out.kWG);
        tKvm += stick() - tk0;

        const int kNsec = 3;
        auto buildKFrames = [&](const std::string& realPayload, int& sidxOut,
                                std::string& framesOut, std::string& plainOut) {
            int realAt = (int)krng.range(kNsec);
            sidxOut = realAt + 1;
            std::vector<std::string> payloads(kNsec);
            payloads[(size_t)realAt] = realPayload;
            for (int i = 0; i < kNsec; ++i) {
                if (i == realAt) continue;
                int dl = 24 + (int)krng.range(40);
                for (int q = 0; q < dl; ++q)
                    payloads[(size_t)i].push_back(
                        (char)(std::uint8_t)krng.range(256));
            }
            std::string frames;
            std::string plain;
            std::uint32_t hdrSt2 = mixIdx(out.blobSalt, 4444ull);
            for (int i = 0; i < kNsec; ++i) {
                std::string pay = encryptStream(
                    payloads[(size_t)i], kSectKeyOf(out.blobSalt, out.buildSeed, i + 1, envF));
                std::uint32_t salt = sectionSalt(out.blobSalt, i + 1);
                W fh;
                fh.u4((std::uint32_t)pay.size());
                fh.u4(checksum32(pay, salt));
                plain.append(fh.b);
                plain.append(pay);
                for (size_t q = 0; q < fh.b.size(); ++q) {
                    hdrSt2 = lehmer(hdrSt2);
                    fh.b[(size_t)q] = (char)((std::uint8_t)fh.b[(size_t)q] ^ (std::uint8_t)(hdrSt2 & 0xFFu));
                }
                frames.append(fh.b);
                frames.append(pay);
            }
            framesOut = frames;
            plainOut = plain;
        };
        double tf0 = stick();
        buildKFrames(inner.b, out.kSIdx, out.kblob, out.kFoldView);
        buildKFrames(innerG.b, out.kSIdxG, out.ghostBlob, out.kFoldViewG);
        tKvm += stick() - tf0;

        if (std::getenv("EXF_INNER_DBG")) {
            std::ofstream inf(std::getenv("EXF_INNER_DBG"), std::ios::binary);
            inf << inner.b;
        }
        if (std::getenv("EXF_KDBG")) {
            std::ofstream kf(std::getenv("EXF_KDBG"), std::ios::binary);
            kf << out.kblob;
            std::cerr << "kSlot=" << out.kSlot << " kLay=" << out.kLay
                      << " kSIdx=" << out.kSIdx
                      << " kPA=" << out.kPA << " kPB=" << out.kPB
                      << " kPC=" << out.kPC << " kPS=" << out.kPS
                      << " kPK=" << out.kPK << " kG1=" << out.kG1 << "\n";
            std::cerr << "sectKeys:"
                      << " k1=" << kSectKeyOf(out.blobSalt, out.buildSeed, 1, envF)
                      << " k2=" << kSectKeyOf(out.blobSalt, out.buildSeed, 2, envF)
                      << " k3=" << kSectKeyOf(out.blobSalt, out.buildSeed, 3, envF)
                      << " salt=" << out.blobSalt << " seed=" << out.buildSeed
                      << " csMid=" << cs[(size_t)(totalMiddle + 1)]
                      << " csVb=" << cs[(size_t)(totalMiddle + 2)] << "\n";
            for (int c = 0; c < kNop; ++c)
                std::cerr << "canon" << c << "->" << out.kOpIds[(size_t)c] << "\n";
            for (int phase = 0; phase < 5; ++phase) {
                std::cerr << "prog" << phase << ":\n";
                for (size_t pc2 = 1; pc2 <= progs[(size_t)phase].size(); ++pc2) {
                    const KIns& q = progs[(size_t)phase][(size_t)(pc2 - 1)];
                    std::cerr << "  " << pc2 << ": op=" << q.op << " a=" << q.a
                              << " b=" << q.b << " c=" << q.c << " tgt=" << q.tgt << "\n";
                }
            }
        }
    }

    double s1 = stick();
    if (std::getenv("EXF_DUMP_BLOB")) {
        std::ofstream df(std::getenv("EXF_DUMP_BLOB"), std::ios::binary);
        df << out.blob;
    }
    double s2 = stick();
    if (stiming) {
        std::fprintf(stderr, "TIME3 protoLoop=%.1f packFinal=%.1f | instr=%.1f az=%.1f enc=%.1f sbox=%.1f kvm=%.1f\n",
                     s1 - s0, s2 - s1, tLoop, tAz, tEnc, tSbox, tKvm);
    }
    return out;
}

}
}
