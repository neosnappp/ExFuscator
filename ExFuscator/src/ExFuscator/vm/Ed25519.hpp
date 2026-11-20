/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include <cstddef>
#include <cstdint>

namespace astra {
namespace ed25519 {

extern const std::uint8_t kPublisherSeed[32];

void sha512(const std::uint8_t* data, std::size_t len, std::uint8_t out[64]);

const std::uint8_t* publisherPubkey();

void sign(const std::uint8_t* msg, std::size_t len, std::uint8_t sig[64]);

bool verify(const std::uint8_t pk[32], const std::uint8_t* msg, std::size_t len,
            const std::uint8_t sig[64]);

}
}
