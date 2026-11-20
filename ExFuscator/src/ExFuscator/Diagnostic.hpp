/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include "astra/Common.hpp"

namespace astra {

struct AstraError : public std::exception {
    std::string message;
    int line = 0, col = 0;

    AstraError(std::string msg, int ln = 0, int cl = 0)
        : message(std::move(msg)), line(ln), col(cl) {}

    const char* what() const noexcept override { return message.c_str(); }

    std::string pretty(const std::string& file) const {
        std::ostringstream os;
        if (line > 0)
            os << file << ":" << line << ":" << col << ": " << message;
        else
            os << file << ": " << message;
        return os.str();
    }
};

}
