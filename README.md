<img width="2172" height="724" alt="ExFuscator" src="https://github.com/user-attachments/assets/d571e0ab-da6a-4707-be25-fffe49d00a13" />



# ExFuscator

### What is ExFuscator?

ExFuscator is a Lua obfuscator built to push the limits of code obfuscation.

### Is it vibe-coded?

Yeah it is. But just because something is vibe-coded doesn't automatically mean its not secure

Besides i think spending countless hours manually developing an obfuscator in 2026 is pretty pointless, especially with how powerful ai models like Opus 5.5, GPT 6.2 Astra, Fable 5.2, and others have become

With enough time and resources even the strongest obfuscation can eventually be deobfuscated.

### Will there be more updates?

Of course. I'm not planning to spend too much time working on this thing, but I'll still release updates whenever I feel like it.

### Can people make a deobfuscator for ExFuscator?

Of course. Nothing is impossible to reverse-engineer.

ExFuscator simply aims to make the process harder through custom-encoded bytecode, a register-based virtual machine, encoded strings, and more...

since it's open-source, analyzing it and developing a deobfuscator will be easier.

### Will you create a Discord server for ExFuscator?

If ExFuscator gets enough attention and people actually start using it, I'll consider opening a Discord server


# ExFuscator — USAGE GUIDE

( this written by glm 5.3 )

## What is ExFuscator?
ExFuscator is a commercial-grade obfuscator for Lua/Luau, written in C++17. It turns your script into protected output that is extremely hard to read, analyze or modify — safe from script stealers, decompilers and static analysis. Every build is verified to behave identically to the original.

## How It Protects Your Code

**ExVM Virtualization — always active**
Your script is compiled into custom encrypted bytecode running on an embedded register-based virtual machine. The output contains no readable Lua logic — no structure, no names, no constants. Every build shuffles its own opcode table, so each generated file is unique.

**String Encryption**
Every string literal is encrypted. Plaintext strings never appear in the output — they are decrypted only at runtime.

**Number Encoding**
Numeric constants are rewritten as arithmetic expressions, hiding offsets, keys and identifiers.

**Identifier Renaming**
All local names are replaced with meaningless generated identifiers that can never collide with your source.

**Control Flow Flattening**
Loops and branches are rebuilt into dispatcher-style flow, so the original logic tree becomes invisible. Intensity adapts automatically to file size.

**Opaque Predicates**
Fake conditions that always resolve one way but are practically impossible to evaluate statically — they poison static analysis.

**Call Proxies**
Function calls are routed through generated indirection layers, breaking call-graph analysis.

**Dead Code Injection**
Realistic fake code blocks are inserted around your real logic.

**Data-Flow Masking**
Intermediate values are transformed so the actual data flow cannot be traced.

**Tamper Detection**
The output verifies its own integrity: any edit or truncation stops the script safely with a typed error — no crash, no hint.

## Build
```bash 
build.bat       # Windows (MSVC)
```

## Quick Start
```bash
./exfuscator script.lua                              # default (medium)
./exfuscator script.lua -o protected.lua             # custom output path
./exfuscator script.lua --preset maximum --seed 777  # strongest + reproducible
```

## Presets
**`light`** — fastest runtime: identifier renaming, minification and full ExVM virtualization. Use when execution speed is critical.

**`medium`** *(default)* — balanced protection: adds string encryption, number encoding, control-flow flattening, call proxies and opaque predicates.

**`maximum`** — strongest protection: everything enabled, including global renaming and heavy dead code injection. Larger output, maximum resistance.

ExVM virtualization is always active in every preset — your code never ships as readable Lua.

## Options
```
-o, --output <file>   output path (default: out.lua)
--preset <name>       light | medium | maximum
--seed <n>            same seed = identical output (reproducible)
--rename-globals      rename globals too (advanced)
-q, --quiet           no console output
-h, --help            help
```

## Tips
- Always test the obfuscated output before distributing
- The same --seed reproduces the exact same file
- Output too large? Use --preset medium instead of maximum
- Script runs slow? Use --preset light
-# © kYro — ExFuscator ( glm 5.3 )

