/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include "astra/vm/VmSerializer.hpp"

namespace astra {
namespace vm {

std::string emitVmOutput(const VmBuild& b, std::uint64_t seed, const std::string& watermark);

}
}
