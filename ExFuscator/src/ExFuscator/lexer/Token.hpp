#pragma once

#include "astra/Common.hpp"

namespace astra {

enum class TokType {
    Eof,
    Name,
    Number,
    String,
    Interp,
    Keyword,
    Op,
};

struct Token {
    TokType type = TokType::Eof;
    std::string text;
    std::string bytes;
    double num = 0.0;
    int line = 1;
    int col = 1;
    std::vector<std::pair<bool, std::string>> segs;

    bool is(TokType t) const { return type == t; }
    bool isKw(const char* kw) const { return type == TokType::Keyword && text == kw; }
    bool isOp(const char* o) const { return type == TokType::Op && text == o; }
};

extern const std::set<std::string> kKeywords;

inline bool isValidIdentifier(const std::string& s) {
    if (s.empty()) return false;
    if (!(std::isalpha((unsigned char)s[0]) || s[0] == '_')) return false;
    for (char c : s)
        if (!(std::isalnum((unsigned char)c) || c == '_')) return false;
    return !kKeywords.count(s);
}

}
