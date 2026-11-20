#pragma once

#include "astra/lexer/Token.hpp"

namespace astra {

class Lexer {
public:
    Lexer(std::string source, std::string filename);

    std::vector<Token> tokenize();

private:
    std::string src_;
    std::string file_;
    size_t pos_ = 0;
    int line_ = 1, col_ = 1;

    char cur() const;
    char at(size_t off) const;
    bool eof() const;
    char advance();
    bool match(char c);
    [[noreturn]] void fail(const std::string& msg);

    void skipWhitespaceAndComments();
    Token lexName();
    Token lexNumber();
    Token lexShortString(char quote);
    Token lexInterpString();
    Token lexLongString(int level);
    Token lexOp();

    std::string readEscapeSequence(char quote);
    static int hexVal(char c);
};

}
