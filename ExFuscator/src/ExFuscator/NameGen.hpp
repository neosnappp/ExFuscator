/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include "astra/Common.hpp"

namespace astra {

class NameGen {
public:
    explicit NameGen(std::unordered_set<std::string> avoid = {})
        : avoid_(std::move(avoid)), index_(0) {}

    void reserve(const std::string& name) { avoid_.insert(name); }

    void reserveMany(const std::unordered_set<std::string>& names) {
        for (const auto& n : names) avoid_.insert(n);
    }

    std::string next() {
        for (;;) {
            std::string cand = make(index_++);
            if (avoid_.count(cand)) continue;
            if (isReserved(cand)) continue;
            avoid_.insert(cand);
            return cand;
        }
    }

private:

    static bool isReserved(const std::string& s) {
        static const std::unordered_set<std::string> kw = {
            "and", "break", "do", "else", "elseif", "end", "false",
            "for", "function", "goto", "if", "in", "local", "nil",
            "not", "or", "repeat", "return", "then", "true", "until",
            "while", "continue", "self"
        };
        return kw.count(s) != 0;
    }

    static std::string make(std::uint64_t i) {
        std::string s;
        ++i;
        while (i > 0) {
            --i;
            s.insert(s.begin(), (char)('a' + (char)(i % 26)));
            i /= 26;
        }
        return s;
    }

    std::unordered_set<std::string> avoid_;
    std::uint64_t index_;
};

}
