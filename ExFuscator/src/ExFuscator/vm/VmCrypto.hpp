/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include "astra/Common.hpp"

namespace astra {
namespace vm {

constexpr std::uint32_t kMod31 = 2147483647u;
constexpr std::uint32_t kMask24 = 16777216u;
constexpr std::uint32_t kMask16 = 65536u;

struct BuildConsts {
    std::uint32_t m4;
    std::uint32_t ma;
    std::uint32_t mb;
    std::uint32_t mc;
    std::uint32_t md;
    std::uint32_t me;
    std::uint32_t sa;
    std::uint32_t sb;
    std::uint32_t sc;
    std::uint32_t sd;
    std::uint32_t pr;
    std::uint32_t ckW;
    std::uint32_t ckA;
    std::uint32_t cmM;
    std::uint32_t ivM;
    std::uint32_t s4a;
    std::uint32_t s4b;
    std::uint32_t va;
    std::uint32_t vb2;
    std::uint32_t vc;
    std::uint32_t vd2;
    std::uint32_t cmM2;
    std::uint32_t ivM2;
    std::uint32_t sfM;
    std::uint32_t ikP;
    std::uint32_t ikV1;
    std::uint32_t ikV2;
    std::uint32_t ik4;
    std::uint32_t ik5;
    std::uint32_t ik6;
    std::uint32_t ikO;
    std::uint32_t ikB;
    std::uint32_t ikS;
};

inline BuildConsts g_bc = {
    16807u, 2654435761u, 48271u, 40503u, 40507u,
    9113823u, 911382u, 911383u, 77003u, 911u, 1000003u,
    89u, 3u, 33u, 1u, 33u, 7u, 3u, 5u, 7u, 11u,
    40503u, 7u, 40507u,
    5013u, 776u, 887u, 7173u, 9451u, 5177u, 6161u, 6263u, 9753u};

inline std::uint32_t rnd31(std::uint32_t& st, std::uint32_t lo, std::uint32_t hi) {
    st = (std::uint32_t)(((std::uint64_t)st * 1103515245ull + 12345ull) % 2147483647ull);
    if (st < 1u) st += 2147483646u;
    std::uint64_t span = (std::uint64_t)hi - lo + 1ull;
    return (std::uint32_t)(lo + (std::uint64_t)st % span);
}

inline std::uint32_t powmod31(std::uint64_t b, std::uint64_t e) {
    std::uint64_t r = 1;
    b %= kMod31;
    while (e) {
        if (e & 1ull) r = r * b % kMod31;
        b = b * b % kMod31;
        e >>= 1;
    }
    return (std::uint32_t)r;
}

inline bool isPrimeW(std::uint64_t n) {
    if (n < 2ull) return false;
    for (std::uint64_t p : {2ull, 3ull, 5ull, 7ull, 11ull, 13ull, 17ull, 19ull,
                            23ull, 29ull, 31ull, 37ull}) {
        if (n % p == 0ull) return n == p;
    }
    std::uint64_t d = n - 1ull;
    int r = 0;
    while (!(d & 1ull)) { d >>= 1; ++r; }
    for (std::uint64_t a : {2ull, 3ull, 5ull, 7ull, 11ull, 13ull, 17ull, 19ull,
                            23ull, 29ull, 31ull, 37ull}) {
        std::uint64_t x = 1;
        std::uint64_t base = a % n;
        std::uint64_t e = d;
        while (e) {
            if (e & 1ull) x = x * base % n;
            base = base * base % n;
            e >>= 1;
        }
        if (x == 1ull || x == n - 1ull) continue;
        bool ok = false;
        for (int i = 0; i < r - 1; ++i) {
            x = x * x % n;
            if (x == n - 1ull) { ok = true; break; }
        }
        if (!ok) return false;
    }
    return true;
}

inline void pickBuildConsts(std::uint32_t seed) {
    std::uint32_t st = seed % 2147483646u;
    if (st < 1u) st += 2147483646u;
    std::uint64_t k = rnd31(st, (1u << 24), (1u << 30));
    k |= 1ull;
    for (int g = 0; g < 64; ++g) {
        if (k % 3ull != 0ull && k % 7ull != 0ull && k % 11ull != 0ull &&
            k % 31ull != 0ull && k % 151ull != 0ull && k % 331ull != 0ull)
            break;
        k += 2ull;
        if (k >= (1ull << 30)) k = (1ull << 24) | 1ull;
    }
    g_bc.m4 = powmod31(7ull, k);
    for (int t3 = 0; t3 < 4096 && g_bc.m4 >= (1u << 22); ++t3) {
        std::uint64_t k2 = rnd31(st, (1u << 24), (1u << 30));
        k2 |= 1ull;
        for (int g2 = 0; g2 < 64; ++g2) {
            if (k2 % 3ull != 0ull && k2 % 7ull != 0ull && k2 % 11ull != 0ull &&
                k2 % 31ull != 0ull && k2 % 151ull != 0ull && k2 % 331ull != 0ull)
                break;
            k2 += 2ull;
            if (k2 >= (1ull << 30)) k2 = (1ull << 24) | 1ull;
        }
        g_bc.m4 = powmod31(7ull, k2);
    }

    if (g_bc.m4 >= (1u << 22)) g_bc.m4 = (g_bc.m4 % ((1u << 22) - 1u)) | 1u;
    if (g_bc.m4 < 65537u) g_bc.m4 = 16807u;
    g_bc.ma = rnd31(st, (1u << 25), (1u << 28) - 1u) | 1u;
    g_bc.mb = rnd31(st, (1u << 16), (1u << 21) - 1u) | 1u;
    g_bc.mc = rnd31(st, (1u << 16), (1u << 21) - 1u) | 1u;
    g_bc.md = rnd31(st, (1u << 16), (1u << 21) - 1u) | 1u;
    g_bc.me = rnd31(st, (1u << 20), (1u << 24) - 1u) | 1u;
    g_bc.sa = rnd31(st, 1u, 2147483646u);
    g_bc.sb = rnd31(st, (1u << 16), (1u << 20) - 1u) | 1u;
    g_bc.sc = rnd31(st, 1u, 2147483646u);
    g_bc.sd = rnd31(st, (1u << 16), (1u << 21) - 1u) | 1u;
    for (int t2 = 0; t2 < 4096; ++t2) {
        std::uint32_t cand = rnd31(st, 100003u, 99999991u);
        if ((cand & 1u) == 0u) ++cand;
        if (isPrimeW(cand)) { g_bc.pr = cand; break; }
        if (t2 == 4095) g_bc.pr = 1000003u;
    }
    g_bc.ckW = rnd31(st, 89u, 8191u) | 1u;
    g_bc.ckA = rnd31(st, 1u, 65535u);
    g_bc.cmM = rnd31(st, 3u, 65535u) | 1u;
    g_bc.ivM = rnd31(st, 1u, 65535u);
    g_bc.s4a = rnd31(st, 3u, 65535u) | 1u;
    g_bc.s4b = rnd31(st, 1u, 2147483645u);
    g_bc.va = rnd31(st, 3u, (1u << 20) - 1u) | 1u;
    g_bc.vb2 = rnd31(st, 1u, (1u << 21) - 1u);
    g_bc.vc = rnd31(st, 1u, 2147483646u);
    g_bc.vd2 = rnd31(st, 1u, 2147483646u);
    g_bc.cmM2 = rnd31(st, 3u, 65535u) | 1u;
    g_bc.ivM2 = rnd31(st, 1u, 65535u);
    g_bc.sfM = rnd31(st, 3u, 65535u) | 1u;
    g_bc.ikP = rnd31(st, 4096u, 65535u);
    g_bc.ikV1 = rnd31(st, 512u, 2047u);
    g_bc.ikV2 = rnd31(st, 2048u, 8191u);
    g_bc.ik4 = rnd31(st, 4096u, 65535u);
    g_bc.ik5 = rnd31(st, 4096u, 65535u);
    g_bc.ik6 = rnd31(st, 4096u, 65535u);
    g_bc.ikO = rnd31(st, 4096u, 65535u);
    g_bc.ikB = rnd31(st, 4096u, 65535u);
    g_bc.ikS = rnd31(st, 4096u, 65535u);
}

inline std::uint32_t xor32(std::uint32_t x, std::uint32_t y) {
    return x ^ y;
}

inline std::uint32_t mod31(std::uint64_t x) {
    std::uint32_t r = (std::uint32_t)(x & 0x7FFFFFFFull) +
                      (std::uint32_t)(x >> 31);
    while (r >= 2147483647u) r -= 2147483647u;
    return r;
}

inline std::uint32_t lehmer(std::uint32_t st) {
    std::uint32_t b = mod31((std::uint64_t)st * (std::uint64_t)g_bc.m4);
    b = xor32(b, b >> 7);
    b = mod31((std::uint64_t)b + g_bc.sd);
    if (b < 1u) b += kMod31 - 1u;
    return b;
}

inline std::uint32_t mixIdx(std::uint64_t k, std::uint64_t idx) {
    std::uint32_t a = (std::uint32_t)((k + idx * (std::uint64_t)g_bc.ma) & 0xFFFFFFFFull);
    a = xor32(a, a >> 24);
    a = xor32(a, a >> 13);
    a = mod31((std::uint64_t)a + g_bc.mb);
    if (a < 1u) a += kMod31 - 1u;
    return a;
}

inline std::uint32_t checksum32(const std::string& s, std::uint32_t salt) {
    std::uint32_t h = salt;
    for (size_t i = 0; i < s.size(); ++i) {
        std::uint32_t i1 = (std::uint32_t)(i + 1);
        std::uint32_t w = (i1 % g_bc.ckW) + g_bc.ckA;
        h += (std::uint32_t)(std::uint8_t)s[i] * w + i1;
        if ((i1 & 15u) == 0u) h = xor32(h, (h >> 16) + i1);
    }
    h = xor32(h, h >> 15);
    h = (std::uint32_t)(((std::uint64_t)h * g_bc.cmM + g_bc.ivM) & 0xFFFFFFFFull);
    h = xor32(h, h >> 13);
    h = (std::uint32_t)(((std::uint64_t)h * g_bc.cmM2 + g_bc.ivM2) & 0xFFFFFFFFull);
    h = xor32(h, h >> 16);
    return h;
}

inline std::uint32_t strideFold(const std::string& s) {
    std::uint32_t h = 0;
    for (size_t i = 0; i < s.size(); i += 7) {
        std::uint32_t i1 = (std::uint32_t)(i + 1);
        std::uint32_t w = (std::uint32_t)(std::uint8_t)s[i] * ((i1 % 89u) + 3u) + i1;
        h = (std::uint32_t)(((std::uint64_t)h * g_bc.sfM +
                            (std::uint64_t)xor32(w, h >> 16)) & 0xFFFFFFFFull);
    }
    h = xor32(h, h >> 11);
    h = (std::uint32_t)(((std::uint64_t)h * g_bc.cmM2 + g_bc.ivM2) & 0xFFFFFFFFull);
    return h;
}

inline std::uint32_t protoKeyOf(std::uint32_t buildSeed, int protoId) {
    std::uint64_t v = ((std::uint64_t)buildSeed + (std::uint64_t)protoId * (std::uint64_t)g_bc.ma) % kMod31;
    if (v < 1) v += 2147483646ull;
    return (std::uint32_t)v;
}

inline std::uint32_t strKeyOf(std::uint32_t protoKey, int strIdx) {
    std::uint64_t v = ((std::uint64_t)protoKey + (std::uint64_t)strIdx * (std::uint64_t)g_bc.me) %
                      2147483646ull;
    v = lehmer((std::uint32_t)v);
    v = ((std::uint32_t)v * (std::uint64_t)g_bc.s4a + (std::uint64_t)g_bc.s4b) % 2147483646ull;
    v = lehmer((std::uint32_t)v);
    std::uint32_t r = xor32((std::uint32_t)v, (std::uint32_t)v >> 7) % 2147483646u;
    return r + 1ull;
}

inline std::uint32_t sectionSalt(std::uint32_t blobSalt, int sectionIdx) {
    return blobSalt + (std::uint32_t)sectionIdx * g_bc.mc;
}

inline std::uint32_t jumpMask(std::uint32_t protoKey, int instrIdx, int opid) {
    return mixIdx(protoKey, ((std::uint64_t)instrIdx * 4ull + 2ull) * 97ull +
                             (std::uint64_t)opid * 13ull) % kMask24;
}

inline std::uint32_t jumpDyn(std::uint32_t protoKey, int instrIdx, int opid) {
    return mixIdx(protoKey, ((std::uint64_t)instrIdx * 4ull + 3ull) * 97ull +
                             (std::uint64_t)opid * 29ull) % kMask24;
}

inline std::uint32_t key2Of(std::uint32_t protoKey, std::uint32_t blobSalt) {
    std::uint64_t v = ((std::uint64_t)protoKey + (std::uint64_t)blobSalt * (std::uint64_t)g_bc.sb +
                       (std::uint64_t)g_bc.sc) % kMod31;
    if (v < 1) v += 2147483646ull;
    return (std::uint32_t)v;
}

struct PcMask {
    std::uint8_t a[8];
    std::uint8_t b[8];
    std::uint8_t j[3];
    bool hasB = false;
    std::uint8_t saltOp = 0;
    std::uint32_t permSeed = 0;
    std::uint32_t permSeed2 = 0;
};

inline PcMask pcMaskOf(std::uint32_t key, std::uint32_t key2, int instrIdx, bool layer2,
                       bool needJ = false, bool needPerm2 = false) {
    PcMask m;
    std::uint32_t s0 = mixIdx(key, (std::uint64_t)instrIdx);
    std::uint32_t a1 = lehmer(s0);
    std::uint32_t a2 = lehmer(a1);
    m.a[0] = (std::uint8_t)(a1 & 0xFFu);
    m.a[1] = (std::uint8_t)((a1 >> 8) & 0xFFu);
    m.a[2] = (std::uint8_t)((a1 >> 16) & 0xFFu);
    m.a[3] = (std::uint8_t)((a1 >> 24) & 0xFFu);
    m.a[4] = (std::uint8_t)(a2 & 0xFFu);
    m.a[5] = (std::uint8_t)((a2 >> 8) & 0xFFu);
    m.a[6] = (std::uint8_t)((a2 >> 16) & 0xFFu);
    m.a[7] = (std::uint8_t)((a2 >> 24) & 0xFFu);
    std::uint32_t a3 = lehmer(a2);
    m.saltOp = (std::uint8_t)(a3 % 251u);
    m.permSeed = lehmer(a3);

    m.permSeed2 = needPerm2 ? lehmer(m.permSeed) : 0u;
    if (needJ) {
        std::uint32_t j0 = mixIdx(key, (std::uint64_t)instrIdx * 4ull + 3ull);
        std::uint32_t j1 = lehmer(j0);
        std::uint32_t j2 = lehmer(j1);
        std::uint32_t j3 = lehmer(j2);
        m.j[0] = (std::uint8_t)(j3 & 0xFFu);
        m.j[1] = (std::uint8_t)((j3 >> 8) & 0xFFu);
        m.j[2] = (std::uint8_t)((j3 >> 16) & 0xFFu);
    }
    if (layer2) {
        m.hasB = true;
        std::uint32_t t0 = mixIdx(key2, (std::uint64_t)instrIdx);
        std::uint32_t b1 = lehmer(t0);
        std::uint32_t b2 = lehmer(b1);
        m.b[0] = (std::uint8_t)(b1 & 0xFFu);
        m.b[1] = (std::uint8_t)((b1 >> 8) & 0xFFu);
        m.b[2] = (std::uint8_t)((b1 >> 16) & 0xFFu);
        m.b[3] = (std::uint8_t)((b1 >> 24) & 0xFFu);
        m.b[4] = (std::uint8_t)(b2 & 0xFFu);
        m.b[5] = (std::uint8_t)((b2 >> 8) & 0xFFu);
        m.b[6] = (std::uint8_t)((b2 >> 16) & 0xFFu);
        m.b[7] = (std::uint8_t)((b2 >> 24) & 0xFFu);
    }
    return m;
}

inline std::uint32_t loadMask(std::uint32_t protoKey, int instrIdx) {
    return mixIdx(protoKey, (std::uint64_t)instrIdx * 4ull + 1ull) % kMask24;
}

inline std::uint32_t kMaskOf(std::uint32_t protoKey, int instrIdx) {
    return mixIdx(protoKey, (std::uint64_t)instrIdx * 4ull + 4ull) % kMask16;
}

inline std::uint32_t envFoldOf() {
    static const std::uint32_t pv[9] = {65u, 90u, 9u, 4294967295u, 3u, 3u, 232u, 471u, 250u};
    std::uint32_t h = 7u;
    for (int i = 0; i < 9; ++i)
        h = (std::uint32_t)(((std::uint64_t)h * (19ull + 8ull * (std::uint64_t)(i + 1)) +
                             (std::uint64_t)pv[(size_t)i] + 1ull) % kMod31);
    if (h < 1u) h = 1u;
    return h;
}

inline std::uint32_t vaultKeyOf(std::uint32_t blobSalt, std::uint32_t buildSeed) {
    std::uint64_t v = ((std::uint64_t)blobSalt * g_bc.va +
                       (std::uint64_t)buildSeed * g_bc.vb2 + g_bc.vc +
                       (std::uint64_t)envFoldOf()) % kMod31;
    if (v < 1) v += 2147483646ull;
    return (std::uint32_t)v;
}

inline std::uint32_t kSectKeyOf(std::uint32_t blobSalt, std::uint32_t buildSeed, int idx,
                                std::uint32_t envF) {
    std::uint64_t v = ((std::uint64_t)blobSalt + (std::uint64_t)buildSeed + (std::uint64_t)envF) %
                      kMod31;
    if (v < 1) v += 2147483646ull;
    return mixIdx(v, (std::uint64_t)idx * 2ull + 9ull);
}

struct KStream {
    std::uint8_t k[7];
};

inline KStream kStreamOf(std::uint32_t progKey, int pc) {
    KStream s;
    std::uint32_t s0 = mixIdx(progKey, (std::uint64_t)pc);
    std::uint32_t s1 = lehmer(s0);
    std::uint32_t s2 = lehmer(s1);
    std::uint32_t s3 = lehmer(s2);
    s.k[0] = (std::uint8_t)(s1 & 0xFFu);
    s.k[1] = (std::uint8_t)((s1 >> 8) & 0xFFu);
    s.k[2] = (std::uint8_t)((s1 >> 16) & 0xFFu);
    s.k[3] = (std::uint8_t)((s1 >> 24) & 0xFFu);
    s.k[4] = (std::uint8_t)(s2 & 0xFFu);
    s.k[5] = (std::uint8_t)((s2 >> 8) & 0xFFu);
    s.k[6] = (std::uint8_t)(s3 & 0xFFu);
    return s;
}

inline void protoShuffle(std::vector<int>& p2, std::uint32_t key) {
    for (int i = 1; i <= (int)p2.size() - 1; ++i) p2[i] = i;
    std::uint32_t st = key;
    for (int i = (int)p2.size() - 1; i >= 2; --i) {
        st = lehmer(st);
        int j = 1 + (int)(st % (std::uint32_t)i);
        std::swap(p2[i], p2[j]);
    }
}

inline std::uint8_t encByte(std::uint32_t& st, std::uint8_t plain) {
    st = lehmer(st);
    return (std::uint8_t)(plain ^ (st & 0xFFu));
}

inline std::uint8_t decByte(std::uint32_t& st, std::uint8_t cipher) {
    return encByte(st, cipher);
}

inline void encryptStreamInPlace(std::string& data, std::uint32_t key) {
    std::uint32_t sa = key;
    std::uint32_t sb = mixIdx(key, 707ull);
    for (size_t i = 0; i < data.size(); ++i) {
        std::uint32_t st;
        if (((i + 1) & 1u) == 1u) { sa = lehmer(sa); st = sa; }
        else { sb = lehmer(sb); st = sb; }
        data[i] = (char)((std::uint8_t)data[i] ^ (std::uint8_t)(st & 0xFFu));
    }
}

inline std::string encryptStream(std::string data, std::uint32_t key) {
    encryptStreamInPlace(data, key);
    return data;
}

inline std::string decryptStream(const std::string& data, std::uint32_t key) {
    return encryptStream(data, key);
}

inline void sboxApplyInPlace(std::string& data, const std::vector<std::uint8_t>& sb) {
    for (size_t i = 0; i < data.size(); ++i)
        data[i] = (char)sb[(std::uint8_t)data[i]];
}

inline std::string sboxApply(std::string data, const std::vector<std::uint8_t>& sb) {
    sboxApplyInPlace(data, sb);
    return data;
}

inline std::string encryptStr(std::string data, std::uint32_t key) {
    std::uint32_t st = key;
    for (size_t i = 0; i < data.size(); ++i) {
        st = lehmer(st);
        data[i] = (char)((std::uint8_t)data[i] ^ (std::uint8_t)(st & 0xFFu));
    }
    return data;
}

inline std::vector<std::uint8_t> genSbox(std::uint32_t seed) {
    std::vector<std::uint8_t> s(256);
    for (int i = 0; i < 256; ++i) s[(size_t)i] = (std::uint8_t)i;
    std::uint32_t st = seed % kMod31;
    if (st < 1u) st += 2147483646u;
    for (int i = 255; i >= 1; --i) {
        st = lehmer(st);
        int j = (int)(st % (std::uint32_t)(i + 1));
        std::swap(s[(size_t)i], s[(size_t)j]);
    }
    std::uint32_t st2 = mixIdx(seed % kMod31, 555ull);
    for (int i = 255; i >= 1; --i) {
        st2 = lehmer(st2);
        int j = (int)(st2 % (std::uint32_t)(i + 1));
        std::swap(s[(size_t)i], s[(size_t)j]);
    }
    return s;
}

}
}
