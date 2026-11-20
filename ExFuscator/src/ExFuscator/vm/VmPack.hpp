#pragma once

#include "astra/Common.hpp"
#include "astra/Random.hpp"

namespace astra {
namespace vm {

std::string azPack(const std::string& raw);

std::string b85Alphabet(std::uint32_t buildSeed);

std::string b85Encode(const std::string& in, const std::string& alpha);

}
}
