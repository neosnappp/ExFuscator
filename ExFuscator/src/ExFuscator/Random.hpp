/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include "astra/Common.hpp"

namespace astra {

class Rng {
public:
    explicit Rng(std::uint64_t seed) : state_(seed) {
        for (int i = 0; i < 4; ++i) next();
    }

    std::uint64_t next() {
        std::uint64_t z = (state_ += 0x9E3779B97F4A7C15ULL);
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31);
    }

    std::uint64_t range(std::uint64_t n) {
        return n == 0 ? 0 : next() % n;
    }

    std::int64_t irange(std::int64_t a, std::int64_t b) {
        if (b < a) std::swap(a, b);
        return a + (std::int64_t)range((std::uint64_t)(b - a + 1));
    }

    bool chance(double p) {
        if (p >= 1.0) return true;
        if (p <= 0.0) return false;
        return ((next() >> 11) * (1.0 / 9007199254740992.0)) < p;
    }

    template <typename T>
    const T& pick(const std::vector<T>& v) {
        return v[(size_t)range(v.size())];
    }

    std::uint8_t byte() { return (std::uint8_t)(1 + range(255)); }

private:
    std::uint64_t state_;
};

}
