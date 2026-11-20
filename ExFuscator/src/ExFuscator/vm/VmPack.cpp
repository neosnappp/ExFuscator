/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#include "astra/vm/VmPack.hpp"

#include "astra/vm/VmCrypto.hpp"

#include <vector>

namespace astra {
namespace vm {

namespace {

void pushU4(std::string& s, std::uint32_t v) {
    s.push_back((char)((v >> 24) & 0xFFu));
    s.push_back((char)((v >> 16) & 0xFFu));
    s.push_back((char)((v >> 8) & 0xFFu));
    s.push_back((char)(v & 0xFFu));
}

const size_t kHashSlots = 1u << 17;
const size_t kHashMask = kHashSlots - 1;

const int kMaxChain = 6;

struct PackCtx {
    std::vector<int> head;
    std::vector<unsigned> stamp;
    std::vector<int> prev;
    unsigned gen = 0;
    PackCtx() : head(kHashSlots, -1), stamp(kHashSlots, 0) {}
};

inline size_t hash4(const unsigned char* p, size_t pos) {
    std::uint32_t v = ((std::uint32_t)p[pos] << 20) ^
                      ((std::uint32_t)p[pos + 1] << 12) ^
                      ((std::uint32_t)p[pos + 2] << 4) ^
                      (std::uint32_t)p[pos + 3];
    return (size_t)(v & kHashMask);
}

size_t findMatch(PackCtx& cx, const unsigned char* p, size_t n, size_t i,
                 size_t& bestOff) {
    size_t bestLen = 0;
    bestOff = 0;
    if (i + 4 > n) return 0;
    size_t h = hash4(p, i);
    if (cx.stamp[h] != cx.gen) return 0;
    int c = cx.head[h];
    int depth = kMaxChain;

    size_t maxLen = n - i;
    if (maxLen > 4096) maxLen = 4096;
    while (c >= 0 && depth > 0) {
        size_t pos = (size_t)c;
        size_t dist = i - pos;
        if (dist == 0 || dist > 65535) break;
        if (p[pos] != p[i] || p[pos + bestLen] != p[i + bestLen] ||
            p[pos + 1] != p[i + 1]) {
            c = cx.prev[pos];
            --depth;
            continue;
        }
        size_t l = 2;
        while (l < maxLen && p[pos + l] == p[i + l]) ++l;
        if (l > bestLen) {
            bestLen = l;
            bestOff = dist;
            if (l == maxLen) break;
        }
        c = cx.prev[pos];
        --depth;
    }
    if (bestLen < 4) return 0;
    return bestLen;
}

void insertPos(PackCtx& cx, const unsigned char* p, size_t n, size_t i) {
    if (i + 4 > n) return;
    size_t h = hash4(p, i);
    cx.prev[i] = (cx.stamp[h] == cx.gen) ? cx.head[h] : -1;
    cx.head[h] = (int)i;
    cx.stamp[h] = cx.gen;
}

void flushPend(std::string& body, std::string& pend) {
    if (pend.empty()) return;

    size_t h = body.size();
    body.push_back('\0');
    unsigned ll = (unsigned)pend.size();
    if (ll >= 15) {
        unsigned rem = ll - 15;
        while (rem >= 255) { body.push_back((char)255); rem -= 255; }
        body.push_back((char)rem);
    }
    body += pend;
    body[h] = (char)((unsigned char)(ll < 15 ? ll : 15) << 4);
    pend.clear();
}

}

std::string azPack(const std::string& raw) {
    std::string head;
    head.push_back('\0');
    pushU4(head, (std::uint32_t)raw.size());
    if (raw.size() < 24) {
        head += raw;
        return head;
    }

    static thread_local PackCtx cx;
    ++cx.gen;
    if (cx.gen == 0) {
        std::fill(cx.stamp.begin(), cx.stamp.end(), 0u);
        cx.gen = 1;
    }

    const unsigned char* p = (const unsigned char*)raw.data();
    const size_t n = raw.size();
    if (cx.prev.size() < n) cx.prev.resize(n);

    std::string body;
    std::string pend;
    body.reserve(n);
    size_t i = 0;
    while (i < n) {
        size_t off1 = 0;
        size_t len1 = findMatch(cx, p, n, i, off1);
        if (len1 >= 4 && len1 < 10 && i + 1 < n) {
            size_t off2 = 0;
            size_t len2 = findMatch(cx, p, n, i + 1, off2);
            if (len2 > len1) {
                pend.push_back((char)p[i]);
                insertPos(cx, p, n, i);
                ++i;
                continue;
            }
        }
        if (len1 >= 4) {

            size_t ll = pend.size(), ml = len1 - 3;
            size_t h = body.size();
            body.push_back('\0');
            if (ll >= 15) {
                unsigned rem = (unsigned)(ll - 15);
                while (rem >= 255) { body.push_back((char)255); rem -= 255; }
                body.push_back((char)rem);
            }
            body += pend;
            pend.clear();
            body.push_back((char)(off1 & 0xFFu));
            body.push_back((char)((off1 >> 8) & 0xFFu));
            body[h] = (char)(((unsigned char)(ll < 15 ? ll : 15) << 4) |
                             (unsigned char)(ml < 15 ? ml : 15));
            if (ml >= 15) {
                unsigned rem = (unsigned)(ml - 15);
                while (rem >= 255) { body.push_back((char)255); rem -= 255; }
                body.push_back((char)rem);
            }
            for (size_t q = i; q < i + len1; ++q) insertPos(cx, p, n, q);
            i += len1;
        } else {
            pend.push_back((char)p[i]);
            insertPos(cx, p, n, i);
            ++i;
        }
    }
    flushPend(body, pend);

    if (body.size() + 5 >= raw.size()) {
        head += raw;
        return head;
    }
    head[0] = (char)1;
    pushU4(head, (std::uint32_t)body.size());
    head += body;
    return head;
}

std::string b85Alphabet(std::uint32_t buildSeed) {
    std::vector<char> pool;
    for (int c = 32; c <= 126; ++c) {
        if (c == 34 || c == 92) continue;
        pool.push_back((char)c);
    }
    std::uint32_t st = mixIdx(buildSeed, 404ull);
    for (int i = 92; i >= 1; --i) {
        st = lehmer(st);
        int j = (int)(st % (std::uint32_t)(i + 1));
        std::swap(pool[(size_t)i], pool[(size_t)j]);
    }
    return std::string(pool.begin(), pool.end());
}

std::string b85Encode(const std::string& in, const std::string& alpha) {
    std::string out;
    out.reserve(((in.size() + 3) / 4) * 5);
    size_t i = 0;
    while (i + 4 <= in.size()) {
        std::uint32_t v = (std::uint32_t)(unsigned char)in[i] |
                          ((std::uint32_t)(unsigned char)in[i + 1] << 8) |
                          ((std::uint32_t)(unsigned char)in[i + 2] << 16) |
                          ((std::uint32_t)(unsigned char)in[i + 3] << 24);
        char d[5];
        for (int j = 0; j < 5; ++j) { d[j] = alpha[v % 93u]; v /= 93u; }
        out.append(d, 5);
        i += 4;
    }
    size_t rem = in.size() - i;
    if (rem > 0) {
        std::uint32_t v = 0;
        for (size_t j = 0; j < rem; ++j)
            v |= (std::uint32_t)(unsigned char)in[i + j] << (8 * j);
        char d[5];
        for (int j = 0; j < 5; ++j) { d[j] = alpha[v % 93u]; v /= 93u; }
        out.append(d, rem + 1);
    }
    return out;
}

}
}
