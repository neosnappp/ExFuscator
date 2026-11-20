/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#pragma once

#include <deque>

#include "astra/Common.hpp"
#include "astra/Random.hpp"

namespace astra {
namespace vm {

enum VOp {
    VOP_MOVE = 0, VOP_LOADNIL, VOP_LOADTRUE, VOP_LOADFALSE, VOP_LOADINT, VOP_LOADK,
    VOP_GETGLOBAL, VOP_SETGLOBAL, VOP_GETUPVAL, VOP_SETUPVAL,
    VOP_GETT, VOP_GETT_K, VOP_SETT, VOP_SETT_K, VOP_NEWTABLE, VOP_SETLIST, VOP_SELF, VOP_CONCAT,
    VOP_ADD, VOP_SUB, VOP_MUL, VOP_DIV, VOP_MOD, VOP_POW,
    VOP_ADDK, VOP_SUBK, VOP_MULK, VOP_DIVK, VOP_MODK, VOP_POWK,
    VOP_UNM, VOP_NOT, VOP_LEN,
    VOP_JMP, VOP_IFEQ, VOP_IFNE, VOP_IFLT, VOP_IFLE, VOP_IFGT, VOP_IFGE, VOP_JIFF, VOP_JIFT,
    VOP_IFEK, VOP_IFNK, VOP_FLEQ, VOP_FLNE, VOP_FLLT, VOP_FLLE, VOP_FLGT, VOP_FLGE,
    VOP_CALL, VOP_CALLM, VOP_TAILCALL, VOP_RET, VOP_RETM, VOP_VARARG, VOP_VARARG1, VOP_SPILL,
    VOP_CLOSURE, VOP_CLOSE,
    VOP_FORPREP, VOP_FORLOOP, VOP_TFOR,
    VOP_DISPATCH,
    VOP_GETGF, VOP_SCALL, VOP_RETK,
    VOP_MCALL, VOP_GCALL, VOP_MTAIL, VOP_GTAIL, VOP_KRET, VOP_CRET,
    VOP_SCT, VOP_CRTM,
    VOP_TSETK, VOP_TGET2, VOP_KARITH, VOP_MVSETK,
    VOP_RSUBK, VOP_RDIVK, VOP_RPOWK,
    VOP_ADDI, VOP_SUBI, VOP_MULI,
    VOP_IFLTK, VOP_IFLEK, VOP_IFGTK, VOP_IFGEK,
    VOP_IFKLT, VOP_IFKLE, VOP_IFKGT, VOP_IFKGE,
    VOP_CALL1, VOP_CALL2, VOP_CALL3,
    VOP_RET0, VOP_RET1,
    VOP_GETTK, VOP_GETTRK, VOP_SETTRK,
    VOP_NEWTAB_LIST,
    VOP_LOAD2K, VOP_MOVE2,
    VOP_CONCAT2, VOP_CONCAT3, VOP_CONCATK,
    VOP_GETT_I, VOP_SETT_I,
    VOP_FORPREP1, VOP_FORLOOP1,
    VOP_STATEJMP,

    VOP_TGETC,
    VOP_TADDK,
    VOP_DECOY0 = 114,
    VOP_DECOY11 = 213,
    VOP_COUNT = 214
};

enum VFmtClass {
    VF_R4, VF_R3, VF_A2, VF_K2, VF_J24, VF_ABS24, VF_ABK, VF_KK, VF_JCS16, VF_SCA,
    VF_GCA, VF_ABSK, VF_ABS6, VF_AKK2
};

enum VLayout {
    VL_ABC4 = 0, VL_AB3, VL_A2, VL_AK3, VL_S24, VL_BAC4, VL_BA3,
    VL_KA3, VL_ABK5, VL_KK6, VL_S16C5, VL_ABS24, VL_SCA7, VL_SCK7, VL_ABSK7,
    VL_ABS6, VL_AKK6, VL_COUNT
};

struct VInstr {
    int op = 0;
    int a = 0;
    int b = 0;
    int c = 0;
    std::int64_t s = 0;
    int k = -1;
    int target = -1;
    bool jump = false;
};

struct VConst {
    enum T { NIL, BOOL, NUM, STR } t = NIL;
    bool b = false;
    double n = 0.0;
    std::string s;
};

struct VUpval {
    int kind = 0;
    int idx = 0;
};

struct VProto {
    int nparams = 0;
    bool vararg = false;
    int nregs = 0;
    int regBase = 0;
    std::vector<VUpval> upvals;
    std::vector<VConst> ks;
    std::vector<VInstr> code;
    std::vector<int> children;
    bool flattened = false;
    std::vector<std::pair<int, int>> flat;
};

struct VmIR {
    std::deque<VProto> protos;
    int entry = 0;
};

inline VFmtClass opFmtClass(int op) {
    switch (op) {
        case VOP_MOVE: case VOP_GETT: case VOP_SETT:
        case VOP_ADD: case VOP_SUB: case VOP_MUL: case VOP_DIV: case VOP_MOD: case VOP_POW:
        case VOP_UNM: case VOP_NOT: case VOP_LEN:
        case VOP_CONCAT: case VOP_SETLIST: case VOP_CALL: case VOP_CALLM:
        case VOP_CONCAT2: case VOP_CONCAT3:
            return VF_R4;
        case VOP_IFEK: case VOP_IFNK:
            return VF_ABSK;
        case VOP_FLEQ: case VOP_FLNE: case VOP_FLLT: case VOP_FLLE:
        case VOP_FLGT: case VOP_FLGE:
            return VF_ABS24;
        case VOP_LOADTRUE: case VOP_LOADFALSE: case VOP_GETUPVAL: case VOP_SETUPVAL:
        case VOP_VARARG: case VOP_RET: case VOP_RETM: case VOP_TAILCALL: case VOP_SPILL:
            return VF_R3;
        case VOP_LOADNIL: case VOP_VARARG1: case VOP_CLOSE: case VOP_NEWTABLE: case VOP_DISPATCH:
            return VF_A2;
        case VOP_LOADK: case VOP_GETGLOBAL: case VOP_SETGLOBAL: case VOP_CLOSURE: case VOP_RETK:
            return VF_K2;
        case VOP_GETT_K: case VOP_SETT_K:
        case VOP_ADDK: case VOP_SUBK: case VOP_MULK: case VOP_DIVK: case VOP_MODK: case VOP_POWK:
        case VOP_SELF:
        case VOP_RSUBK: case VOP_RDIVK: case VOP_RPOWK:
        case VOP_IFLTK: case VOP_IFLEK: case VOP_IFGTK: case VOP_IFGEK:
        case VOP_IFKLT: case VOP_IFKLE: case VOP_IFKGT: case VOP_IFKGE:
        case VOP_CONCATK:
            return VF_ABK;
        case VOP_ADDI: case VOP_SUBI: case VOP_MULI:
        case VOP_GETT_I: case VOP_SETT_I:
            return VF_ABS6;
        case VOP_CALL1: case VOP_CALL2: case VOP_CALL3:
        case VOP_RET1: case VOP_NEWTAB_LIST: case VOP_MOVE2:
            return VF_R3;
        case VOP_RET0:
            return VF_A2;
        case VOP_GETTK: case VOP_GETTRK: case VOP_SETTRK:
            return VF_SCA;
        case VOP_LOAD2K:
            return VF_AKK2;
        case VOP_SCALL: case VOP_MCALL: case VOP_MTAIL: case VOP_SCT:
            return VF_SCA;
        case VOP_GCALL: case VOP_GTAIL:
            return VF_GCA;
        case VOP_KRET:
            return VF_ABK;
        case VOP_TSETK:
            return VF_KK;
        case VOP_TGET2: case VOP_KARITH:
        case VOP_TGETC: case VOP_TADDK:
            return VF_GCA;
        case VOP_MVSETK:
            return VF_ABK;
        case VOP_CRET: case VOP_CRTM:
            return VF_R4;
        case VOP_GETGF:
            return VF_KK;
        case VOP_JMP: case VOP_JIFF: case VOP_JIFT: case VOP_FORPREP: case VOP_FORLOOP:
        case VOP_FORPREP1: case VOP_FORLOOP1:
        case VOP_LOADINT:
            return VF_J24;
        case VOP_STATEJMP:
            return VF_J24;
        case VOP_IFEQ: case VOP_IFNE: case VOP_IFLT: case VOP_IFLE: case VOP_IFGT: case VOP_IFGE:
            return VF_ABS24;
        case VOP_TFOR:
            return VF_JCS16;
        default:
            return VF_R4;
    }
}

inline VLayout pickLayout(VFmtClass fc, Rng& rng) {
    switch (fc) {
        case VF_R4: return rng.chance(0.5) ? VL_ABC4 : VL_BAC4;
        case VF_R3: return rng.chance(0.5) ? VL_AB3 : VL_BA3;
        case VF_A2: return VL_A2;
        case VF_K2: return rng.chance(0.5) ? VL_AK3 : VL_KA3;
        case VF_J24: return VL_S24;
        case VF_ABS24: return VL_ABS24;
        case VF_ABK: return VL_ABK5;
        case VF_KK: return VL_KK6;
        case VF_JCS16: return VL_S16C5;
        case VF_SCA: return VL_SCA7;
        case VF_GCA: return VL_SCK7;
        case VF_ABSK: return VL_ABSK7;
        case VF_ABS6: return VL_ABS6;
        case VF_AKK2: return VL_AKK6;
        default: return VL_ABC4;
    }
}

inline int layoutSize(VLayout l) {
    switch (l) {
        case VL_ABC4: return 4;
        case VL_AB3: return 3;
        case VL_A2: return 2;
        case VL_AK3: return 3;
        case VL_S24: return 5;
        case VL_BAC4: return 4;
        case VL_BA3: return 3;
        case VL_KA3: return 3;
        case VL_ABK5: return 5;
        case VL_KK6: return 6;
        case VL_S16C5: return 5;
        case VL_ABS24: return 6;
        case VL_SCA7: return 7;
        case VL_SCK7: return 7;
        case VL_ABSK7: return 7;
        case VL_ABS6: return 6;
        case VL_AKK6: return 6;
        default: return 4;
    }
}

inline bool isJumpOp(int op) {
    return op == VOP_JMP || op == VOP_JIFF || op == VOP_JIFT ||
           op == VOP_FORPREP || op == VOP_FORLOOP || op == VOP_TFOR ||
           op == VOP_FORPREP1 || op == VOP_FORLOOP1 ||
           op == VOP_IFEK || op == VOP_IFNK ||
           (op >= VOP_IFEQ && op <= VOP_IFGE) ||
           (op >= VOP_FLEQ && op <= VOP_FLGE) ||
           (op >= VOP_IFLTK && op <= VOP_IFKGE);
}

inline bool isTermOp(int op) {
    return op == VOP_RET || op == VOP_TAILCALL || op == VOP_MTAIL ||
           op == VOP_GTAIL || op == VOP_KRET || op == VOP_CRET ||
           op == VOP_SCT || op == VOP_CRTM || op == VOP_RET0 || op == VOP_RET1 ||
           isJumpOp(op);
}

}
}
