cmake_minimum_required(VERSION 3.12)
project(Exfuscator CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

add_executable(exfuscator
    src/Main.cpp
    src/exfuscator/Config.cpp
    src/exfuscator/lexer/Lexer.cpp
    src/exfuscator/parser/Parser.cpp
    src/exfuscator/emitter/Emitter.cpp
    src/exfuscator/passes/RenamePass.cpp
    src/exfuscator/cff/CfgFlow.cpp
    src/exfuscator/passes/ProxyPass.cpp
    src/exfuscator/passes/OpaquePass.cpp
    src/exfuscator/passes/StringEncryptPass.cpp
    src/exfuscator/passes/NumberEncodePass.cpp
    src/exfuscator/passes/DeadCodePass.cpp
    src/exfuscator/core/Obfuscator.cpp
    src/exfuscator/vm/VmCodegen.cpp
    src/exfuscator/vm/VmPasses.cpp
    src/exfuscator/vm/VmSerializer.cpp
    src/exfuscator/vm/VmEmitter.cpp
    src/exfuscator/vm/VmPipeline.cpp
)

target_include_directories(exfuscator PRIVATE src)

if(MSVC)
    target_compile_options(exfuscator PRIVATE /O2 /EHsc)
else()
    target_compile_options(exfuscator PRIVATE -O2 -Wall -Wextra)
endif()
