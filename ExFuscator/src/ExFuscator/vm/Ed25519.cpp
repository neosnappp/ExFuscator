/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#include "astra/vm/Ed25519.hpp"
#include "astra/vm/Sha512Consts.hpp"

#include <array>
#include <cstring>
#include <vector>

namespace astra {
namespace ed25519 {

namespace {

typedef std::array<std::uint64_t, 4> Fe;

const Fe kP = {0xFFFFFFFFFFFFFFEDULL, 0xFFFFFFFFFFFFFFFFULL,
               0xFFFFFFFFFFFFFFFFULL, 0x7FFFFFFFFFFFFFFFULL};
const Fe kTwoP = {0xFFFFFFFFFFFFFFDAULL, 0xFFFFFFFFFFFFFFFFULL,
                  0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL};

Fe feFromU64(std::uint64_t v) {
    Fe r = {v, 0, 0, 0};
    return r;
}

bool feGeP(const Fe& a) {
    for (int i = 3; i >= 1; --i) {
        if (a[(size_t)i] != kP[(size_t)i]) return a[(size_t)i] > kP[(size_t)i];
    }
    return a[0] >= kP[0];
}

Fe feCan(Fe r) {

    if (r[3] >> 63) {
        r[3] &= 0x7FFFFFFFFFFFFFFFULL;
        unsigned __int128 cur = (unsigned __int128)r[0] + 19;
        r[0] = (std::uint64_t)cur;
        std::uint64_t carry = (std::uint64_t)(cur >> 64);
        for (int i = 1; i < 4 && carry; ++i) {
            cur = (unsigned __int128)r[(size_t)i] + carry;
            r[(size_t)i] = (std::uint64_t)cur;
            carry = (std::uint64_t)(cur >> 64);
        }
    }

    while (feGeP(r)) {
        std::uint64_t br = 0;
        for (int i = 0; i < 4; ++i) {
            unsigned __int128 diff = (unsigned __int128)r[(size_t)i] - kP[(size_t)i] - br;
            r[(size_t)i] = (std::uint64_t)diff;
            br = (diff >> 64) ? 1 : 0;
        }
    }
    return r;
}

Fe feAdd(const Fe& a, const Fe& b) {
    Fe r;
    std::uint64_t carry = 0;
    for (int i = 0; i < 4; ++i) {
        unsigned __int128 cur = (unsigned __int128)a[(size_t)i] + b[(size_t)i] + carry;
        r[(size_t)i] = (std::uint64_t)cur;
        carry = (std::uint64_t)(cur >> 64);
    }
    return feCan(r);
}

Fe feSub(const Fe& a, const Fe& b) {
    Fe r;
    std::uint64_t br = 0;
    for (int i = 0; i < 4; ++i) {
        unsigned __int128 diff = (unsigned __int128)a[(size_t)i] - b[(size_t)i] - br;
        r[(size_t)i] = (std::uint64_t)diff;
        br = (diff >> 64) ? 1 : 0;
    }
    if (br) {
        std::uint64_t carry = 0;
        for (int i = 0; i < 4; ++i) {
            unsigned __int128 cur = (unsigned __int128)r[(size_t)i] + kTwoP[(size_t)i] + carry;
            r[(size_t)i] = (std::uint64_t)cur;
            carry = (std::uint64_t)(cur >> 64);
        }
    }
    return feCan(r);
}

Fe feMul(const Fe& a, const Fe& b) {
    std::uint64_t t[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    for (int i = 0; i < 4; ++i) {
        unsigned __int128 carry = 0;
        for (int j = 0; j < 4; ++j) {
            unsigned __int128 cur = (unsigned __int128)t[(size_t)(i + j)] +
                                    (unsigned __int128)a[(size_t)i] * b[(size_t)j] + carry;
            t[(size_t)(i + j)] = (std::uint64_t)cur;
            carry = cur >> 64;
        }
        int k = i + 4;
        while (carry && k < 8) {
            unsigned __int128 cur = (unsigned __int128)t[(size_t)k] + (std::uint64_t)carry;
            t[(size_t)k] = (std::uint64_t)cur;
            carry = cur >> 64;
            ++k;
        }
    }

    unsigned __int128 cur = (unsigned __int128)t[0] + (unsigned __int128)t[4] * 38;
    Fe out;
    out[0] = (std::uint64_t)cur;
    unsigned __int128 cr = cur >> 64;
    for (int i = 1; i < 4; ++i) {
        cur = (unsigned __int128)t[(size_t)i] + (unsigned __int128)t[(size_t)(i + 4)] * 38 +
              (std::uint64_t)cr;
        out[(size_t)i] = (std::uint64_t)cur;
        cr = cur >> 64;
    }
    while (cr) {
        cur = (unsigned __int128)out[0] + (std::uint64_t)cr * 38;
        out[0] = (std::uint64_t)cur;
        cr = cur >> 64;
        for (int i = 1; i < 4 && cr; ++i) {
            cur = (unsigned __int128)out[(size_t)i] + (std::uint64_t)cr;
            out[(size_t)i] = (std::uint64_t)cur;
            cr = cur >> 64;
        }
    }
    return feCan(out);
}

Fe feSq(const Fe& a) { return feMul(a, a); }

Fe feNeg(const Fe& a) { return feSub(kTwoP, a); }

bool feBit(const Fe& a, int bit) { return (a[(size_t)(bit >> 6)] >> (bit & 63)) & 1ULL; }

Fe fePow(const Fe& base, const Fe& exp) {
    Fe r = feFromU64(1);
    for (int bit = 255; bit >= 0; --bit) {
        r = feSq(r);
        if (feBit(exp, bit)) r = feMul(r, base);
    }
    return feCan(r);
}

Fe feInv(const Fe& a) { return fePow(a, feSub(kP, feFromU64(2))); }

Fe feFromBytes(const std::uint8_t b[32]) {
    Fe r = {0, 0, 0, 0};
    for (int i = 0; i < 4; ++i) {
        std::uint64_t v = 0;
        for (int j = 7; j >= 0; --j) v = (v << 8) | b[(size_t)(i * 8 + j)];
        r[(size_t)i] = v;
    }
    std::uint64_t sign = r[3] >> 63;
    r[3] &= 0x7FFFFFFFFFFFFFFFULL;
    if (sign) {
        unsigned __int128 cur = (unsigned __int128)r[0] + 19;
        r[0] = (std::uint64_t)cur;
        std::uint64_t carry = (std::uint64_t)(cur >> 64);
        for (int i = 1; i < 4 && carry; ++i) {
            cur = (unsigned __int128)r[(size_t)i] + carry;
            r[(size_t)i] = (std::uint64_t)cur;
            carry = (std::uint64_t)(cur >> 64);
        }
    }
    return feCan(r);
}

void feToBytes(const Fe& x0, std::uint8_t out[32]) {
    Fe x = feCan(x0);
    std::memset(out, 0, 32);
    for (int i = 0; i < 4; ++i) {
        for (int j = 0; j < 8; ++j) {
            out[(size_t)(i * 8 + j)] = (std::uint8_t)(x[(size_t)i] >> (8 * j));
        }
    }
}

bool feEq(const Fe& a, const Fe& b) { return feCan(a) == feCan(b); }

struct Ge {
    Fe X, Y, Z, T;
};

Fe kD, kSqrtm1, kExpSqrt, kBy;
Ge kBase;
bool kInitDone = false;

Ge geIdentity() { return {feFromU64(0), feFromU64(1), feFromU64(1), feFromU64(0)}; }

Ge geAdd(const Ge& P, const Ge& Q) {
    Fe A = feMul(feSub(P.Y, P.X), feSub(Q.Y, Q.X));
    Fe B = feMul(feAdd(P.Y, P.X), feAdd(Q.Y, Q.X));
    Fe C = feMul(P.T, Q.T);
    C = feAdd(C, C);
    C = feMul(C, kD);
    Fe Dv = feMul(P.Z, Q.Z);
    Dv = feAdd(Dv, Dv);
    Fe E = feSub(B, A);
    Fe F = feSub(Dv, C);
    Fe G = feAdd(Dv, C);
    Fe H = feAdd(B, A);
    return {feMul(E, F), feMul(G, H), feMul(F, G), feMul(E, H)};
}

Ge geDbl(const Ge& P) {
    Fe A = feSq(P.X);
    Fe B = feSq(P.Y);
    Fe zs = feSq(P.Z);
    Fe C = feAdd(zs, zs);
    Fe D = feNeg(A);
    Fe E = feSq(feAdd(P.X, P.Y));
    E = feSub(E, A);
    E = feSub(E, B);
    Fe G = feAdd(D, B);
    Fe F = feSub(G, C);
    Fe H = feSub(D, B);
    return {feMul(E, F), feMul(G, H), feMul(F, G), feMul(E, H)};
}

Ge geMuls(const Ge& P, const Fe& s) {
    Ge R = geIdentity();
    bool started = false;
    for (int bit = 255; bit >= 0; --bit) {
        if (started) R = geDbl(R);
        if (feBit(s, bit)) {
            if (started) {
                R = geAdd(R, P);
            } else {
                R = Ge{P.X, P.Y, P.Z, P.T};
                started = true;
            }
        }
    }
    return R;
}

Fe feXrecover(const Fe& y, bool* ok) {
    Fe yy = feSq(y);
    Fe u = feSub(yy, feFromU64(1));
    Fe v = feAdd(feMul(kD, yy), feFromU64(1));
    Fe x = feMul(u, feInv(v));
    x = fePow(x, kExpSqrt);
    Fe chk = feMul(feSq(x), v);
    if (!feEq(chk, u)) {
        if (feEq(chk, feNeg(u))) {
            x = feMul(x, kSqrtm1);
            chk = feMul(feSq(x), v);
            if (!feEq(chk, u)) {
                *ok = false;
                return feFromU64(0);
            }
        } else {
            *ok = false;
            return feFromU64(0);
        }
    }
    if (feBit(x, 0)) x = feNeg(x);
    *ok = true;
    return x;
}

void initCurve() {
    if (kInitDone) return;
    Fe num = feSub(feFromU64(0), feFromU64(121665));
    kD = feMul(num, feInv(feFromU64(121666)));

    Fe e1 = {0xFFFFFFFFFFFFFFFBULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL,
             0x1FFFFFFFFFFFFFFFULL};
    kSqrtm1 = fePow(feFromU64(2), e1);

    kExpSqrt = {0xFFFFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL,
                0x0FFFFFFFFFFFFFFFULL};
    kBy = feMul(feFromU64(4), feInv(feFromU64(5)));
    bool ok = false;
    Fe bx = feXrecover(kBy, &ok);
    kBase = Ge{bx, kBy, feFromU64(1), feMul(bx, kBy)};
    kInitDone = true;
}

const std::uint64_t kL[4] = {0x5812631A5CF5D3EDULL, 0x14DEF9DEA2F79CD6ULL,
                             0x0000000000000000ULL, 0x1000000000000000ULL};

bool scLtL(const std::uint64_t a[4]) {
    for (int i = 3; i >= 0; --i) {
        if (a[i] != kL[i]) return a[i] < kL[i];
    }
    return false;
}

void scModL(const std::uint64_t in[8], std::uint64_t out[4]) {
    std::uint64_t acc[4] = {0, 0, 0, 0};
    int top = 511;
    while (top > 0 && !((in[(size_t)(top >> 6)] >> (top & 63)) & 1ULL)) --top;
    for (int bit = top; bit >= 0; --bit) {
        std::uint64_t carry = (in[(size_t)(bit >> 6)] >> (bit & 63)) & 1ULL;
        for (int i = 0; i < 4; ++i) {
            unsigned __int128 cur = (unsigned __int128)acc[i] * 2 + carry;
            acc[i] = (std::uint64_t)cur;
            carry = (std::uint64_t)(cur >> 64);
        }
        if (!scLtL(acc)) {
            std::uint64_t br = 0;
            for (int i = 0; i < 4; ++i) {
                unsigned __int128 diff = (unsigned __int128)acc[i] - kL[i] - br;
                acc[i] = (std::uint64_t)diff;
                br = (diff >> 64) ? 1 : 0;
            }
        }
    }
    for (int i = 0; i < 4; ++i) out[i] = acc[i];
}

void scMulAdd(const std::uint64_t a[4], const std::uint64_t b[4], const std::uint64_t c[4],
              std::uint64_t out[4]) {
    std::uint64_t prod[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    for (int i = 0; i < 4; ++i) {
        unsigned __int128 carry = 0;
        for (int j = 0; j < 4; ++j) {
            unsigned __int128 cur = (unsigned __int128)prod[(size_t)(i + j)] +
                                    (unsigned __int128)b[i] * c[j] + carry;
            prod[(size_t)(i + j)] = (std::uint64_t)cur;
            carry = cur >> 64;
        }
        int k = i + 4;
        while (carry && k < 8) {
            unsigned __int128 cur = (unsigned __int128)prod[(size_t)k] + (std::uint64_t)carry;
            prod[(size_t)k] = (std::uint64_t)cur;
            carry = cur >> 64;
            ++k;
        }
    }
    std::uint64_t bc[4];
    scModL(prod, bc);
    std::uint64_t sum[4];
    std::uint64_t carry = 0;
    for (int i = 0; i < 4; ++i) {
        unsigned __int128 cur = (unsigned __int128)a[i] + bc[i] + carry;
        sum[i] = (std::uint64_t)cur;
        carry = (std::uint64_t)(cur >> 64);
    }
    if (!scLtL(sum)) {
        std::uint64_t br = 0;
        for (int i = 0; i < 4; ++i) {
            unsigned __int128 diff = (unsigned __int128)sum[i] - kL[i] - br;
            sum[i] = (std::uint64_t)diff;
            br = (diff >> 64) ? 1 : 0;
        }
    }
    for (int i = 0; i < 4; ++i) out[i] = sum[i];
}

Fe scToFe(const std::uint64_t s[4]) { return Fe{s[0], s[1], s[2], s[3]}; }

void geCompress(const Ge& P, std::uint8_t out[32]) {
    Fe zi = feInv(P.Z);
    Fe x = feMul(P.X, zi);
    Fe y = feMul(P.Y, zi);
    feToBytes(y, out);
    std::uint8_t xb[32];
    feToBytes(x, xb);
    out[31] |= (std::uint8_t)((xb[0] & 1) << 7);
}

bool geDecompress(const std::uint8_t* enc, Ge& out) {
    std::uint8_t tmp[32];
    std::memcpy(tmp, enc, 32);
    std::uint64_t sign = tmp[31] >> 7;
    tmp[31] &= 0x7F;
    Fe y = feFromBytes(tmp);
    bool ok = false;
    Fe x = feXrecover(y, &ok);
    if (!ok) return false;
    if (feBit(x, 0) != sign) x = feNeg(x);
    out = Ge{x, y, feFromU64(1), feMul(x, y)};
    return true;
}

}

const std::uint8_t kPublisherSeed[32] = {
    0xcf, 0x08, 0x11, 0x04, 0x8b, 0xe6, 0x3c, 0x44, 0xa0, 0x96, 0x08, 0xa4,
    0x4d, 0x7c, 0xe8, 0x2a, 0x91, 0xca, 0x5c, 0x3f, 0xd9, 0xa6, 0x0f, 0xa7,
    0x38, 0x16, 0xb7, 0x54, 0xbc, 0x49, 0x6d, 0xac};

void sha512(const std::uint8_t* data, std::size_t len, std::uint8_t out[64]) {
    std::uint64_t h[8];
    for (int i = 0; i < 8; ++i) h[i] = kSha512IV[i];
    std::size_t padded = ((len + 17 + 127) / 128) * 128;
    std::vector<std::uint8_t> buf(data, data + len);
    buf.resize(padded, 0);
    buf[len] = 0x80;
    std::uint64_t bits = (std::uint64_t)len * 8;
    for (int i = 0; i < 8; ++i) buf[padded - 1 - (size_t)i] = (std::uint8_t)(bits >> (8 * i));
    for (std::size_t blk = 0; blk < padded / 128; ++blk) {
        std::uint64_t W[80];
        for (int t = 0; t < 16; ++t) {
            const std::uint8_t* p = &buf[blk * 128 + (size_t)t * 8];
            W[t] = ((std::uint64_t)p[0] << 56) | ((std::uint64_t)p[1] << 48) |
                   ((std::uint64_t)p[2] << 40) | ((std::uint64_t)p[3] << 32) |
                   ((std::uint64_t)p[4] << 24) | ((std::uint64_t)p[5] << 16) |
                   ((std::uint64_t)p[6] << 8) | (std::uint64_t)p[7];
        }
        for (int t = 16; t < 80; ++t) {
            std::uint64_t s1 = ((W[t - 2] >> 19) | (W[t - 2] << 45)) ^
                               ((W[t - 2] >> 61) | (W[t - 2] << 3)) ^ (W[t - 2] >> 6);
            std::uint64_t s0 = ((W[t - 15] >> 1) | (W[t - 15] << 63)) ^
                               ((W[t - 15] >> 8) | (W[t - 15] << 56)) ^ (W[t - 15] >> 7);
            W[t] = s1 + W[t - 7] + s0 + W[t - 16];
        }
        std::uint64_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6],
                      hh = h[7];
        for (int t = 0; t < 80; ++t) {
            std::uint64_t S1 = ((e >> 14) | (e << 50)) ^ ((e >> 18) | (e << 46)) ^
                               ((e >> 41) | (e << 23));
            std::uint64_t ch = (e & f) ^ ((~e) & g);
            std::uint64_t T1 = hh + S1 + ch + kSha512K[t] + W[t];
            std::uint64_t S0 = ((a >> 28) | (a << 36)) ^ ((a >> 34) | (a << 30)) ^
                               ((a >> 39) | (a << 25));
            std::uint64_t maj = (a & b) ^ (a & c) ^ (b & c);
            std::uint64_t T2 = S0 + maj;
            hh = g;
            g = f;
            f = e;
            e = d + T1;
            d = c;
            c = b;
            b = a;
            a = T1 + T2;
        }
        h[0] += a;
        h[1] += b;
        h[2] += c;
        h[3] += d;
        h[4] += e;
        h[5] += f;
        h[6] += g;
        h[7] += hh;
    }
    for (int i = 0; i < 8; ++i) {
        for (int j = 0; j < 8; ++j) {
            out[(size_t)(i * 8 + j)] = (std::uint8_t)(h[i] >> (56 - 8 * j));
        }
    }
}

namespace {

struct KeyMat {
    Fe a;
    std::uint8_t prefix[32];
    std::uint8_t pk[32];
};

KeyMat deriveKeys() {
    initCurve();
    KeyMat km;
    std::uint8_t h[64];
    sha512(kPublisherSeed, 32, h);
    std::uint8_t a[32];
    std::memcpy(a, h, 32);
    a[0] &= 248;
    a[31] &= 63;
    a[31] |= 64;
    km.a = {0, 0, 0, 0};
    for (int i = 0; i < 4; ++i) {
        std::uint64_t v = 0;
        for (int j = 7; j >= 0; --j) v = (v << 8) | a[(size_t)(i * 8 + j)];
        km.a[(size_t)i] = v;
    }
    std::memcpy(km.prefix, h + 32, 32);
    Ge A = geMuls(kBase, km.a);
    geCompress(A, km.pk);
    return km;
}

const KeyMat& keys() {
    static KeyMat km = deriveKeys();
    return km;
}

}

const std::uint8_t* publisherPubkey() { return keys().pk; }

void sign(const std::uint8_t* msg, std::size_t len, std::uint8_t sig[64]) {
    const KeyMat& km = keys();
    std::vector<std::uint8_t> buf;
    buf.reserve(96 + len);
    buf.insert(buf.end(), km.prefix, km.prefix + 32);
    buf.insert(buf.end(), msg, msg + len);
    std::uint8_t rh[64];
    sha512(buf.data(), buf.size(), rh);
    std::uint64_t big[8];
    for (int i = 0; i < 8; ++i) {
        std::uint64_t v = 0;
        for (int j = 7; j >= 0; --j) v = (v << 8) | rh[(size_t)(i * 8 + j)];
        big[i] = v;
    }
    std::uint64_t r[4];
    scModL(big, r);
    Ge R = geMuls(kBase, scToFe(r));
    std::uint8_t Rb[32];
    geCompress(R, Rb);

    buf.clear();
    buf.insert(buf.end(), Rb, Rb + 32);
    buf.insert(buf.end(), km.pk, km.pk + 32);
    buf.insert(buf.end(), msg, msg + len);
    std::uint8_t kh[64];
    sha512(buf.data(), buf.size(), kh);
    for (int i = 0; i < 8; ++i) {
        std::uint64_t v = 0;
        for (int j = 7; j >= 0; --j) v = (v << 8) | kh[(size_t)(i * 8 + j)];
        big[i] = v;
    }
    std::uint64_t k[4];
    scModL(big, k);
    std::uint64_t aLimbs[4] = {km.a[0], km.a[1], km.a[2], km.a[3]};
    std::uint64_t S[4];
    scMulAdd(r, k, aLimbs, S);
    std::memcpy(sig, Rb, 32);
    for (int i = 0; i < 4; ++i) {
        for (int j = 0; j < 8; ++j) {
            sig[32 + (size_t)(i * 8 + j)] = (std::uint8_t)(S[i] >> (8 * j));
        }
    }
}

bool verify(const std::uint8_t pk[32], const std::uint8_t* msg, std::size_t len,
            const std::uint8_t sig[64]) {
    initCurve();
    std::uint64_t s[4];
    for (int i = 0; i < 4; ++i) {
        std::uint64_t v = 0;
        for (int j = 7; j >= 0; --j) v = (v << 8) | sig[32 + (size_t)(i * 8 + j)];
        s[i] = v;
    }
    if (!scLtL(s)) return false;
    Ge R, A;
    if (!geDecompress(sig, R)) return false;
    if (!geDecompress(pk, A)) return false;
    std::vector<std::uint8_t> buf;
    buf.reserve(64 + len);
    buf.insert(buf.end(), sig, sig + 32);
    buf.insert(buf.end(), pk, pk + 32);
    buf.insert(buf.end(), msg, msg + len);
    std::uint8_t kh[64];
    sha512(buf.data(), buf.size(), kh);
    std::uint64_t big[8];
    for (int i = 0; i < 8; ++i) {
        std::uint64_t v = 0;
        for (int j = 7; j >= 0; --j) v = (v << 8) | kh[(size_t)(i * 8 + j)];
        big[i] = v;
    }
    std::uint64_t k[4];
    scModL(big, k);
    Ge P1 = geMuls(kBase, scToFe(s));
    Ge P2 = geAdd(R, geMuls(A, scToFe(k)));
    std::uint8_t c1[32], c2[32];
    geCompress(P1, c1);
    geCompress(P2, c2);
    return std::memcmp(c1, c2, 32) == 0;
}

}
}
