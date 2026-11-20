#include "astra/lexer/Lexer.hpp"
#include "astra/Diagnostic.hpp"

namespace astra {

const std::set<std::string> kKeywords = {
    "and", "break", "do", "else", "elseif", "end", "false", "for",
    "function", "if", "in", "local", "nil", "not", "or", "repeat",
    "return", "then", "true", "until", "while",
    "continue",
};

Lexer::Lexer(std::string source, std::string filename)
    : src_(std::move(source)), file_(std::move(filename)) {}

char Lexer::cur() const { return pos_ < src_.size() ? src_[pos_] : '\0'; }
char Lexer::at(size_t off) const { return pos_ + off < src_.size() ? src_[pos_ + off] : '\0'; }
bool Lexer::eof() const { return pos_ >= src_.size(); }

char Lexer::advance() {
    char c = src_[pos_++];
    if (c == '\n') { ++line_; col_ = 1; }
    else ++col_;
    return c;
}

bool Lexer::match(char c) {
    if (cur() == c) { advance(); return true; }
    return false;
}

void Lexer::fail(const std::string& msg) {
    throw AstraError(msg, line_, col_);
}

int Lexer::hexVal(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

void Lexer::skipWhitespaceAndComments() {
    for (;;) {
        while (!eof() && std::isspace((unsigned char)cur())) advance();

        if (pos_ == 0 && cur() == '#' && at(1) == '!') {
            while (!eof() && cur() != '\n') advance();
            continue;
        }

        if (cur() == '-' && at(1) == '-') {
            advance(); advance();

            if (cur() == '[') {
                int level = 0;
                size_t save = pos_;
                advance();
                while (cur() == '=') { advance(); ++level; }
                if (cur() == '[') {
                    advance();
                    for (;;) {
                        if (eof()) fail("unterminated long comment");
                        if (cur() == ']' ) {
                            size_t sp = pos_;
                            advance();
                            int lv = 0;
                            while (cur() == '=' && lv < level) { advance(); ++lv; }
                            if (lv == level && cur() == ']') { advance(); break; }
                            if (lv != level) pos_ = sp + 1, col_ += 1;
                        } else {
                            advance();
                        }
                    }
                    continue;
                }
                pos_ = save;
            }

            while (!eof() && cur() != '\n') advance();
            continue;
        }
        break;
    }
}

std::vector<Token> Lexer::tokenize() {
    std::vector<Token> out;

    out.reserve(src_.size() / 5 + 16);
    for (;;) {
        skipWhitespaceAndComments();
        Token t;
        t.line = line_;
        t.col = col_;
        if (eof()) {
            t.type = TokType::Eof;
            out.push_back(t);
            return out;
        }
        char c = cur();
        if (std::isalpha((unsigned char)c) || c == '_') {
            out.push_back(lexName());
        } else if (std::isdigit((unsigned char)c) ||
                   (c == '.' && std::isdigit((unsigned char)at(1)))) {
            out.push_back(lexNumber());
        } else if (c == '"' || c == '\'') {
            out.push_back(lexShortString(c));
        } else if (c == '`') {
            out.push_back(lexInterpString());
        } else if (c == '[' && (at(1) == '[' || at(1) == '=')) {

            int level = 0;
            size_t save = pos_;
            advance();
            while (cur() == '=') { advance(); ++level; }
            if (cur() == '[') {
                advance();
                out.push_back(lexLongString(level));
            } else {
                pos_ = save; col_ -= (level + 1);
                out.push_back(lexOp());
            }
        } else {
            out.push_back(lexOp());
        }
    }
}

Token Lexer::lexName() {
    Token t;
    t.line = line_; t.col = col_;
    std::string s;
    while (!eof() && (std::isalnum((unsigned char)cur()) || cur() == '_'))
        s += advance();
    t.text = s;
    t.type = kKeywords.count(s) ? TokType::Keyword : TokType::Name;
    return t;
}

Token Lexer::lexNumber() {
    Token t;
    t.line = line_; t.col = col_;
    std::string raw;

    if (cur() == '0' && (at(1) == 'x' || at(1) == 'X')) {
        raw += advance(); raw += advance();
        while (!eof() && (hexVal(cur()) >= 0 || cur() == '_' || cur() == '.')) raw += advance();

        if (cur() == 'p' || cur() == 'P') {
            raw += advance();
            if (cur() == '+' || cur() == '-') raw += advance();
            while (!eof() && (std::isdigit((unsigned char)cur()) || cur() == '_')) raw += advance();
        }
    } else {
        while (!eof() && (std::isdigit((unsigned char)cur()) || cur() == '_')) raw += advance();
        if (cur() == '.') {
            raw += advance();
            while (!eof() && (std::isdigit((unsigned char)cur()) || cur() == '_')) raw += advance();
        }
        if (cur() == 'e' || cur() == 'E') {
            raw += advance();
            if (cur() == '+' || cur() == '-') raw += advance();
            while (!eof() && (std::isdigit((unsigned char)cur()) || cur() == '_')) raw += advance();
        }
    }

    std::string clean;
    for (char c : raw)
        if (c != '_') clean += c;

    char* endp = nullptr;
    double val = std::strtod(clean.c_str(), &endp);
    if (endp == clean.c_str())
        fail("malformed number near '" + raw + "'");

    t.type = TokType::Number;
    t.text = raw;
    t.num = val;
    return t;
}

std::string Lexer::readEscapeSequence(char ) {

    advance();
    char c = cur();
    switch (c) {
        case 'a': advance(); return "\a";
        case 'b': advance(); return "\b";
        case 'f': advance(); return "\f";
        case 'n': advance(); return "\n";
        case 'r': advance(); return "\r";
        case 't': advance(); return "\t";
        case 'v': advance(); return "\v";
        case '\\': advance(); return "\\";
        case '"': advance(); return "\"";
        case '\'': advance(); return "'";
        case '\n': advance(); return "\n";
        case 'x': {
            advance();
            int v = 0, n = 0;
            while (n < 2 && hexVal(cur()) >= 0) { v = v * 16 + hexVal(cur()); advance(); ++n; }
            if (n == 0) fail("hexadecimal digit expected in \\x escape");
            return std::string(1, (char)v);
        }
        case 'z': {
            advance();
            while (!eof() && std::isspace((unsigned char)cur())) advance();
            return "";
        }
        case 'u': {
            advance();
            if (!match('{')) fail("missing '{' in \\u{xxxx} escape");
            unsigned cp = 0;
            if (hexVal(cur()) < 0) fail("hexadecimal digit expected in \\u escape");
            while (hexVal(cur()) >= 0) { cp = cp * 16 + (unsigned)hexVal(cur()); advance(); }
            if (!match('}')) fail("missing '}' in \\u{xxxx} escape");
            std::string u;
            if (cp < 0x80) u += (char)cp;
            else if (cp < 0x800) {
                u += (char)(0xC0 | (cp >> 6));
                u += (char)(0x80 | (cp & 0x3F));
            } else if (cp < 0x10000) {
                u += (char)(0xE0 | (cp >> 12));
                u += (char)(0x80 | ((cp >> 6) & 0x3F));
                u += (char)(0x80 | (cp & 0x3F));
            } else {
                u += (char)(0xF0 | (cp >> 18));
                u += (char)(0x80 | ((cp >> 12) & 0x3F));
                u += (char)(0x80 | ((cp >> 6) & 0x3F));
                u += (char)(0x80 | (cp & 0x3F));
            }
            return u;
        }
        default:
            if (std::isdigit((unsigned char)c)) {
                int v = 0, n = 0;
                while (n < 3 && std::isdigit((unsigned char)cur())) {
                    v = v * 10 + (cur() - '0');
                    advance(); ++n;
                }
                if (v > 255) fail("decimal escape too large");
                return std::string(1, (char)v);
            }
            fail("invalid escape sequence \\" + std::string(1, c));
    }
    return "";
}

Token Lexer::lexShortString(char quote) {
    Token t;
    t.line = line_; t.col = col_;
    advance();
    std::string bytes;
    for (;;) {
        if (eof()) fail("unterminated string");
        char c = cur();
        if (c == quote) { advance(); break; }
        if (c == '\n') fail("unfinished string");
        if (c == '\\') {
            bytes += readEscapeSequence(quote);
        } else {
            bytes += advance();
        }
    }
    t.type = TokType::String;
    t.bytes = bytes;
    return t;
}

Token Lexer::lexLongString(int level) {
    Token t;
    t.line = line_; t.col = col_;

    if (cur() == '\r') advance();
    if (cur() == '\n') advance();
    std::string bytes;
    for (;;) {
        if (eof()) fail("unterminated long string");
        if (cur() == ']') {
            size_t sp = pos_;
            advance();
            int lv = 0;
            while (cur() == '=' && lv < level) { advance(); ++lv; }
            if (lv == level && cur() == ']') {
                advance();
                break;
            }
            if (lv != level) {
                bytes += ']';
                pos_ = sp + 1;
                col_ += 1;
                continue;
            }
        }
        bytes += advance();
    }
    t.type = TokType::String;
    t.bytes = bytes;
    return t;
}

Token Lexer::lexOp() {
    Token t;
    t.line = line_; t.col = col_;
    static const char* three[] = {"...", "//=", "..=", nullptr};
    static const char* two[] = {
        "==", "~=", "<=", ">=", "..", "//", "+=", "-=", "*=", "/=", "%=", "^=", nullptr};
    char c = advance();
    std::string s(1, c);

    {
        char buf[4] = {c, cur(), at(1), 0};
        for (int i = 0; three[i]; ++i)
            if (std::string(buf).substr(0, 3) == three[i]) {
                advance(); advance();
                t.type = TokType::Op; t.text = three[i];
                return t;
            }
    }

    {
        char buf[3] = {c, cur(), 0};
        for (int i = 0; two[i]; ++i)
            if (std::string(buf) == two[i]) {
                advance();
                t.type = TokType::Op; t.text = two[i];
                return t;
            }
    }
    switch (c) {
        case '+': case '-': case '*': case '/': case '%': case '^': case '#':
        case '=': case '<': case '>': case '(': case ')': case '{': case '}':
        case '[': case ']': case ';': case ':': case ',': case '.':
            t.type = TokType::Op; t.text = s;
            return t;
        default:
            fail("unexpected symbol near '" + s + "'");
    }
    t.type = TokType::Op; t.text = s;
    return t;
}
Token Lexer::lexInterpString() {
    Token t;
    t.line = line_; t.col = col_;
    t.type = TokType::Interp;
    t.text = "`";
    advance();
    std::vector<std::pair<bool, std::string>> segs;
    std::string lit;
    auto flushLit = [&]() {
        if (!lit.empty()) { segs.push_back(std::make_pair(false, lit)); lit.clear(); }
    };
    while (!eof()) {
        char c = cur();
        if (c == '`') {
            advance();
            flushLit();
            t.segs = std::move(segs);
            return t;
        }
        if (c == '}') {
            if (at(1) == '}') { advance(); advance(); lit += '}'; continue; }
            lit += advance();
            continue;
        }
        if (c == '{') {
            if (at(1) == '{') { advance(); advance(); lit += '{'; continue; }
            advance();
            flushLit();
            std::string ex;
            int depth = 1;
            while (!eof()) {
                char q = cur();
                if (q == '"' || q == '\'') {
                    char qq2 = q;
                    ex += advance();
                    while (!eof()) {
                        char w = cur();
                        if (w == '\\') { ex += advance(); if (!eof()) ex += advance(); continue; }
                        ex += advance();
                        if (w == qq2) break;
                    }
                    continue;
                }
                if (q == '{') { ++depth; ex += advance(); continue; }
                if (q == '}') {
                    --depth;
                    if (depth == 0) { advance(); break; }
                    ex += advance();
                    continue;
                }
                ex += advance();
            }
            if (depth != 0) fail("unterminated interpolation expression");
            if (ex.empty()) fail("empty interpolation expression");
            segs.push_back(std::make_pair(true, ex));
            continue;
        }
        if (c == '\\') {
            advance();
            if (eof()) fail("unterminated interpolation string");
            char e = cur();
            if (e == 'n') { lit += '\n'; advance(); }
            else if (e == 't') { lit += '\t'; advance(); }
            else if (e == 'r') { lit += '\r'; advance(); }
            else if (e == '`') { lit += '`'; advance(); }
            else if (e == '\\') { lit += '\\'; advance(); }
            else if (e == '"') { lit += '"'; advance(); }
            else if (e == '\'') { lit += '\''; advance(); }
            else if (e == '{') { lit += '{'; advance(); }
            else if (e == '}') { lit += '}'; advance(); }
            else if (e == 'u') {
                advance();
                if (cur() != '{') fail("malformed \\u escape");
                advance();
                std::string h;
                while (!eof() && hexVal(cur()) >= 0) h += advance();
                if (cur() == '}') advance(); else fail("malformed \\u escape");
                unsigned long v = 0;
                for (char hc : h) v = v * 16 + (unsigned long)hexVal(hc);
                if (v < 0x80) lit += (char)v;
                else if (v < 0x800) { lit += (char)(0xC0 | (v >> 6)); lit += (char)(0x80 | (v & 63)); }
                else if (v < 0x10000) { lit += (char)(0xE0 | (v >> 12)); lit += (char)(0x80 | ((v >> 6) & 63)); lit += (char)(0x80 | (v & 63)); }
                else { lit += (char)(0xF0 | (v >> 18)); lit += (char)(0x80 | ((v >> 12) & 63)); lit += (char)(0x80 | ((v >> 6) & 63)); lit += (char)(0x80 | (v & 63)); }
            }
            else fail("invalid escape in interpolation string");
            continue;
        }
        lit += advance();
    }
    fail("unterminated interpolation string");
    return t;
}
}
