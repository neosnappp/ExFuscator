#include "astra/vm/VmCodegen.hpp"

#include <cmath>
#include <cstdio>
#include <iostream>
#include <cstdlib>
#include <unordered_set>

namespace astra {
namespace vm {

namespace {

int swapCompareOp(int op) {
    switch (op) {
        case VOP_IFLT: return VOP_IFGT;
        case VOP_IFLE: return VOP_IFGE;
        case VOP_IFGT: return VOP_IFLT;
        case VOP_IFGE: return VOP_IFLE;
        default: return op;
    }
}

int complementOp(int op) {
    switch (op) {
        case VOP_IFEQ: return VOP_IFNE;
        case VOP_IFNE: return VOP_IFEQ;
        case VOP_IFLT: return VOP_IFGE;
        case VOP_IFLE: return VOP_IFGT;
        case VOP_IFGT: return VOP_IFLE;
        case VOP_IFGE: return VOP_IFLT;
        case VOP_JIFF: return VOP_JIFT;
        case VOP_JIFT: return VOP_JIFF;
        case VOP_IFEK: return VOP_IFNK;
        case VOP_IFNK: return VOP_IFEK;
        case VOP_IFLTK: return VOP_IFGEK;
        case VOP_IFLEK: return VOP_IFGTK;
        case VOP_IFGTK: return VOP_IFLEK;
        case VOP_IFGEK: return VOP_IFLTK;
        case VOP_IFKLT: return VOP_IFKGE;
        case VOP_IFKLE: return VOP_IFKGT;
        case VOP_IFKGT: return VOP_IFKLE;
        case VOP_IFKGE: return VOP_IFKLT;
        case VOP_FLEQ: return VOP_FLNE;
        case VOP_FLNE: return VOP_FLEQ;
        case VOP_FLLT: return VOP_FLGE;
        case VOP_FLLE: return VOP_FLGT;
        case VOP_FLGT: return VOP_FLLE;
        case VOP_FLGE: return VOP_FLLT;
        default: return op;
    }
}

bool onlyAReg(int op) {
    switch (op) {
        case VOP_LOADK: case VOP_GETGLOBAL: case VOP_SETGLOBAL: case VOP_CLOSURE:
        case VOP_RETK: case VOP_LOADINT: case VOP_LOADNIL: case VOP_LOADTRUE:
        case VOP_LOADFALSE: case VOP_NEWTABLE: case VOP_DISPATCH: case VOP_VARARG:
        case VOP_VARARG1: case VOP_GETUPVAL: case VOP_SETUPVAL: case VOP_JIFF:
        case VOP_JIFT: case VOP_JMP: case VOP_CALL: case VOP_CALLM: case VOP_TAILCALL:
        case VOP_SPILL: case VOP_SETLIST: case VOP_FORPREP: case VOP_FORLOOP:
        case VOP_TFOR: case VOP_RET: case VOP_RETM: case VOP_CLOSE: case VOP_GETGF:
        case VOP_GCALL: case VOP_GTAIL: case VOP_TSETK:
        case VOP_RET0: case VOP_FORPREP1: case VOP_FORLOOP1: case VOP_LOAD2K:
            return true;
        default:
            return false;
    }
}

bool isCountB(int op) {
    switch (op) {
        case VOP_RET: case VOP_RETM: case VOP_TAILCALL: case VOP_CALL:
        case VOP_CALLM: case VOP_SPILL: case VOP_VARARG: case VOP_SETLIST:
        case VOP_CRET: case VOP_CRTM: case VOP_CALL1: case VOP_CALL2:
        case VOP_CALL3: case VOP_NEWTAB_LIST:
            return true;
        default:
            return false;
    }
}

bool exitsBlock(int op, bool jump) {
    if (jump) return true;
    return op == VOP_RET || op == VOP_RETM || op == VOP_TAILCALL ||
           op == VOP_MTAIL || op == VOP_GTAIL || op == VOP_KRET ||
           op == VOP_CRET || op == VOP_SCT || op == VOP_CRTM ||
           op == VOP_RET0 || op == VOP_RET1;
}

bool hardExit(int op, bool jump) {
    if (!jump) return op == VOP_RET || op == VOP_RETM || op == VOP_TAILCALL ||
                      op == VOP_MTAIL || op == VOP_GTAIL || op == VOP_KRET ||
                      op == VOP_CRET || op == VOP_SCT || op == VOP_CRTM ||
                      op == VOP_RET0 || op == VOP_RET1;
    return op == VOP_JMP || op == VOP_FORPREP;
}

struct BlockInfo {
    int origStart = -1;
    int start = 0;
    int end = 0;
    int fall = -1;
    int fallBlk = -1;
    int newStart = -1;
    bool term = false;
};

std::vector<BlockInfo> blockify(const VProto& p) {
    std::vector<BlockInfo> list;
    int n = (int)p.code.size();
    if (n == 0) return list;
    std::vector<char> leader(n, 0);
    leader[0] = 1;
    for (const VInstr& in : p.code)
        if (in.jump && in.target >= 0 && in.target < n) leader[in.target] = 1;
    for (int i = 0; i < n; ++i)
        if (exitsBlock(p.code[i].op, p.code[i].jump) && i + 1 < n) leader[i + 1] = 1;
    for (int i = 0; i < n; ++i) {
        if (leader[i]) {
            BlockInfo b;
            b.origStart = i;
            b.start = i;
            list.push_back(b);
        }
    }
    for (size_t bi = 0; bi < list.size(); ++bi) {
        int bend = (bi + 1 < list.size()) ? list[bi + 1].start - 1 : n - 1;
        list[bi].end = bend;
        const VInstr& in = p.code[bend];
        if (hardExit(in.op, in.jump)) {
            list[bi].term = true;
        } else {
            list[bi].fall = bend + 1;
            list[bi].term = true;
        }
    }
    for (size_t bi = 0; bi < list.size(); ++bi) {
        if (list[bi].fall < 0) continue;
        for (size_t bj = 0; bj < list.size(); ++bj)
            if (list[bj].origStart == list[bi].fall) {
                list[bi].fallBlk = (int)bj;
                break;
            }
    }
    return list;
}

void normalizeFallthroughs(VProto& p, std::vector<BlockInfo>& blocks,
                           std::vector<int>& tmap) {
    std::vector<VInstr> out;
    tmap.assign((size_t)p.code.size(), -1);
    for (BlockInfo& b : blocks) {
        int bstart = (int)out.size();
        for (int i = b.start; i <= b.end; ++i) {
            tmap[i] = (int)out.size();
            out.push_back(p.code[i]);
        }
        if (b.fall >= 0) {
            VInstr jm;
            jm.op = VOP_JMP;
            jm.jump = true;
            jm.target = b.fall;
            out.push_back(jm);
        }
        b.start = bstart;
        b.end = (int)out.size() - 1;
    }
    for (auto& in : out)
        if (in.jump && in.target >= 0 && in.target < (int)tmap.size())
            in.target = tmap[in.target];
    p.code = std::move(out);
}

std::vector<char> hotRanges(const VProto& p);

bool regIsFreshInt(const std::vector<char>& leader, const VProto& p, size_t i, int reg) {
    (void)p;
    if (reg <= 0) return false;
    int j = (int)i - 1;
    while (j >= 0) {
        const VInstr& q = p.code[(size_t)j];
        if (leader[(size_t)j] || q.jump) return false;
        switch (q.op) {
            case VOP_LOADINT:
                if (q.a == reg) return true;
                break;
            case VOP_CALL: case VOP_CALLM: case VOP_TAILCALL:
            case VOP_VARARG: case VOP_VARARG1: case VOP_SPILL:
            case VOP_SETLIST: case VOP_TFOR: case VOP_FORPREP:
            case VOP_FORLOOP: case VOP_FORPREP1: case VOP_FORLOOP1:
            case VOP_NEWTAB_LIST:
                if (reg >= q.a) return false;
                break;
            default:
                if (q.a == reg) return false;
                break;
        }
        --j;
    }
    return false;
}

bool opWritesSingleA(int op) {
    switch (op) {
        case VOP_MOVE: case VOP_LOADNIL: case VOP_LOADTRUE: case VOP_LOADFALSE:
        case VOP_LOADINT: case VOP_LOADK: case VOP_GETGLOBAL: case VOP_GETUPVAL:
        case VOP_NEWTABLE: case VOP_GETT: case VOP_GETT_K:
        case VOP_ADD: case VOP_SUB: case VOP_MUL: case VOP_DIV: case VOP_MOD:
        case VOP_POW: case VOP_ADDK: case VOP_SUBK: case VOP_MULK: case VOP_DIVK:
        case VOP_MODK: case VOP_POWK: case VOP_UNM: case VOP_NOT: case VOP_LEN:
        case VOP_ADDI: case VOP_SUBI: case VOP_MULI: case VOP_RSUBK:
        case VOP_RDIVK: case VOP_RPOWK: case VOP_KARITH: case VOP_TGET2:
        case VOP_TGETC: case VOP_TADDK: case VOP_GETT_I: case VOP_CONCATK:
        case VOP_CONCAT2: case VOP_GETTK: case VOP_GETTRK: case VOP_GETGF:
        case VOP_VARARG1: case VOP_SELF:
            return true;
        default:
            return false;
    }
}

bool opReadsFieldsOnly(int op) {
    switch (op) {
        case VOP_SETGLOBAL: case VOP_SETUPVAL: case VOP_SETT: case VOP_SETT_K:
        case VOP_SETT_I: case VOP_SETTRK: case VOP_TSETK: case VOP_MVSETK:
        case VOP_KRET: case VOP_RETK: case VOP_RET0: case VOP_RET1:
        case VOP_DISPATCH: case VOP_STATEJMP:
            return true;
        default:
            return false;
    }
}

bool regDeadAfter(const VProto& p, size_t start, int reg) {
    if (reg <= 0) return false;
    const size_t n = p.code.size();
    size_t cap = start + 512;
    if (cap > n) cap = n;
    for (size_t j = start; j < cap; ++j) {
        const VInstr& q = p.code[j];
        const int a = q.a, b = q.b, c = q.c;
        if (q.jump) return false;
        if (opWritesSingleA(q.op)) {
            if (b == reg || c == reg) return false;
            if (a == reg) return true;
            continue;
        }
        if (opReadsFieldsOnly(q.op)) {
            if (a == reg || b == reg || c == reg) return false;
            continue;
        }
        if (q.op >= VOP_DECOY0 && q.op <= VOP_DECOY11) {

            if (b == reg || c == reg) return false;
            if (a == reg) return true;
            continue;
        }
        switch (q.op) {
            case VOP_CLOSURE: case VOP_CLOSE:
                return false;
            case VOP_CALL: case VOP_CALLM:

                if (reg >= a && reg <= a + b + 1) return false;
                continue;
            case VOP_CALL1: case VOP_CALL2: case VOP_CALL3:
                if (reg >= a && reg <= a + (q.op == VOP_CALL1 ? 1
                          : q.op == VOP_CALL2 ? 2 : 3)) return false;
                continue;
            case VOP_MCALL: case VOP_GCALL:

                if (a == reg) return true;
                if (reg >= a + 1 && reg <= a + b) return false;
                continue;
            case VOP_SCALL:
                if (a == reg) return true;
                if (reg >= a + 1 && reg <= a + b) return false;
                continue;
            case VOP_MTAIL: case VOP_GTAIL:
                if (a == reg) return true;
                if (reg >= a + 1 && reg <= a + b) return false;
                continue;
            case VOP_TAILCALL: case VOP_RET:
                if (reg >= a && reg <= a + b) return false;
                continue;
            case VOP_RETM:
                if (reg >= a && reg <= a + c + 1) return false;
                continue;
            case VOP_CRTM:
                if (reg >= a && reg <= a + c + 1) return false;
                continue;
            case VOP_CRET:
                if (reg >= a && reg <= a + c + 1) return false;
                continue;
            case VOP_SPILL:
                if (a == reg) return false;
                if (reg >= a + 1 && reg <= a + c) return true;
                continue;
            case VOP_VARARG:
                if (c == 0) {
                    if (a == reg) return true;
                } else if (reg >= a && reg <= a + c - 2) return true;
                continue;
            case VOP_SETLIST:

                if (reg >= a && reg <= a + b) return false;
                continue;
            case VOP_CONCAT:

                if (reg >= b && reg <= c) return false;
                if (a == reg) return true;
                continue;
            case VOP_CONCAT3:
                if (b == reg || c + 1 == reg || c + 2 == reg) return false;
                if (a == reg) return true;
                continue;
            case VOP_LOAD2K: case VOP_MOVE2:
                if (a == reg) return true;
                if (q.op == VOP_MOVE2 && c + 1 == reg) return false;
                continue;
            case VOP_NEWTAB_LIST:
                if (a == reg) return true;
                if (reg >= a + 1 && reg <= a + c + 1) return false;
                continue;
            case VOP_TFOR:
                if (reg >= a && reg <= a + 2 + c + 1) return false;
                continue;
            default:
                return false;
        }
    }
    if (cap < n) return false;
    return true;
}

void passArithProto(VProto& p, Rng& rng, double chance) {
    std::vector<VInstr> out;
    std::vector<int> map(p.code.size(), -1);

    std::vector<char> leader(p.code.size(), 0);
    for (const VInstr& q : p.code)
        if (q.jump && q.target >= 0 && q.target < (int)p.code.size())
            leader[(size_t)q.target] = 1;
    int treg = p.nregs + 1;
    bool usedT = false;
    for (size_t i = 0; i < p.code.size(); ++i) {
        const VInstr& in = p.code[i];
        map[i] = (int)out.size();
        int src = -1;
        if ((in.op == VOP_ADD || in.op == VOP_SUB) && rng.chance(chance)) {
            if (regIsFreshInt(leader, p, i, in.c)) src = 0;
            else if (in.op == VOP_ADD && regIsFreshInt(leader, p, i, in.b)) src = 1;
        }
        if (src >= 0 && src <= 1) {
            VInstr un;
            un.op = VOP_UNM;
            un.a = treg;
            un.b = src == 0 ? in.c : in.b;
            out.push_back(un);
            VInstr nx = in;
            nx.op = (in.op == VOP_ADD) ? VOP_SUB : VOP_ADD;
            if (src == 0) {
                nx.c = treg;
            } else {
                nx.b = in.c;
                nx.c = treg;
            }
            out.push_back(nx);
            usedT = true;
            continue;
        }
        out.push_back(in);
    }
    if (usedT) p.nregs += 1;
    for (auto& in : out)
        if (in.jump && in.target >= 0 && in.target < (int)map.size() && map[in.target] >= 0)
            in.target = map[in.target];
    p.code = std::move(out);
}

void passBranchXformProto(VProto& p, Rng& rng, double chance) {
    std::vector<char> hot = hotRanges(p);
    std::vector<VInstr> out;
    std::vector<int> map(p.code.size(), -1);
    std::vector<std::pair<int, int>> patch;
    for (size_t i = 0; i < p.code.size(); ++i) {
        VInstr in = p.code[i];
        map[i] = (int)out.size();
        if (in.jump && in.target >= 0 && !hot[(size_t)i] && rng.chance(chance)) {
            int op = in.op;
            if (op == VOP_JMP || op == VOP_FORPREP || op == VOP_FORLOOP ||
                op == VOP_TFOR || op == VOP_FORPREP1 || op == VOP_FORLOOP1) {
                patch.push_back({(int)out.size(), in.target});
                out.push_back(in);
                continue;
            }
            bool swapped = false;
            int swappedOp = op;
            if (op >= VOP_IFEQ && op <= VOP_IFGE && rng.chance(0.5)) {
                swapped = true;
                swappedOp = swapCompareOp(op);
            }
            bool invert = rng.chance(0.5);
            int finalOp = invert ? complementOp(swappedOp) : swappedOp;
            int ia = in.a, ib = in.b;
            if (swapped) std::swap(ia, ib);
            VInstr c1;
            c1.op = finalOp;
            c1.a = ia;
            c1.b = ib;
            c1.c = in.c;
            c1.k = in.k;
            c1.jump = true;
            if (invert) {
                c1.target = (int)out.size() + 2;
                out.push_back(c1);
                VInstr jm;
                jm.op = VOP_JMP;
                jm.jump = true;
                jm.target = in.target;
                patch.push_back({(int)out.size(), in.target});
                out.push_back(jm);
            } else {
                c1.target = in.target;
                patch.push_back({(int)out.size(), in.target});
                out.push_back(c1);
            }
            continue;
        }
        if (in.jump && in.target >= 0) {
            patch.push_back({(int)out.size(), in.target});
        }
        out.push_back(in);
    }
    for (const auto& pp : patch) {
        int pos = pp.first;
        int oldT = pp.second;
        if (oldT >= 0 && oldT < (int)map.size() && map[oldT] >= 0) {
            out[(size_t)pos].target = map[oldT];
        }
    }
    p.code = std::move(out);
}

void passFuseProto(VProto& p, Rng& rng, double chance) {

    static const bool noLive = std::getenv("EXF_NO_LIVE") != nullptr;
    static const bool noTgetc = std::getenv("EXF_NO_TGETC") != nullptr;
    static const bool noTaddk = std::getenv("EXF_NO_TADDK") != nullptr;
    std::vector<char> hot = hotRanges(p);
    std::vector<VInstr>& c = p.code;
    std::vector<VInstr> out;
    std::vector<int> map(c.size(), -1);
    std::vector<char> leader(c.size(), 0);
    for (const VInstr& q : c)
        if (q.jump && q.target >= 0 && q.target < (int)c.size())
            leader[(size_t)q.target] = 1;
    size_t i = 0;
    while (i < c.size()) {
        const VInstr& in = c[i];
        bool fused = false;
        if (i + 1 < c.size() && rng.chance(chance) && !hot[(size_t)i] && !leader[(size_t)(i + 1)]) {
            const VInstr& nx = c[i + 1];
            if (in.op == VOP_GETT_K && nx.op == VOP_CALL && nx.a == in.a) {
                VInstr f;
                f.op = VOP_MCALL;
                f.a = in.a;
                f.b = in.b;
                f.k = in.k;
                f.c = nx.c;
                f.s = nx.b;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_GETT_K && nx.op == VOP_TAILCALL &&
                       nx.a == in.a && nx.b >= 1) {
                VInstr f;
                f.op = VOP_MTAIL;
                f.a = in.a;
                f.b = in.b;
                f.k = in.k;
                f.s = nx.b;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_GETT_K &&
                       (nx.op == VOP_CALL1 || nx.op == VOP_CALL2 ||
                        nx.op == VOP_CALL3) && nx.a == in.a) {
                VInstr f;
                f.op = VOP_MCALL;
                f.a = in.a;
                f.b = in.b;
                f.k = in.k;
                f.c = nx.b;
                f.s = nx.op == VOP_CALL1 ? 2 : nx.op == VOP_CALL2 ? 3 : 4;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_GETT_K && nx.op == VOP_RET &&
                       nx.a == in.a && nx.b == 2) {
                VInstr f;
                f.op = VOP_KRET;
                f.a = in.a;
                f.b = in.b;
                f.k = in.k;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_CALLM && nx.op == VOP_RET &&
                       nx.a == in.a && in.c == 0 && nx.b == 0) {
                VInstr f;
                f.op = VOP_CRTM;
                f.a = in.a;
                f.b = in.b;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_CALL && nx.op == VOP_RET &&
                       nx.a == in.a && in.c == 0 && nx.b == 0) {
                VInstr f;
                f.op = VOP_CRET;
                f.a = in.a;
                f.b = in.b;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_GETGLOBAL && nx.op == VOP_GETT_K &&
                       nx.b == in.a) {
                bool three = false;
                if (i + 2 < c.size() && !leader[(size_t)(i + 2)]) {
                    const VInstr& n2 = c[i + 2];
                    if (n2.op == VOP_CALL && n2.a == nx.a) {
                        VInstr f;
                        f.op = VOP_GCALL;
                        f.a = nx.a;
                        f.b = nx.k;
                        f.k = in.k;
                        f.c = n2.c;
                        f.s = n2.b;
                        out.push_back(f);
                        map[i] = (int)out.size() - 1;
                        map[i + 1] = (int)out.size() - 1;
                        map[i + 2] = (int)out.size() - 1;
                        i += 3;
                        fused = true;
                        three = true;
                    } else if (n2.op == VOP_TAILCALL && n2.a == nx.a &&
                               n2.b >= 1) {
                        VInstr f;
                        f.op = VOP_GTAIL;
                        f.a = nx.a;
                        f.b = nx.k;
                        f.k = in.k;
                        f.s = n2.b;
                        out.push_back(f);
                        map[i] = (int)out.size() - 1;
                        map[i + 1] = (int)out.size() - 1;
                        map[i + 2] = (int)out.size() - 1;
                        i += 3;
                        fused = true;
                        three = true;
                    }
                }
                if (!three) {
                    VInstr f;
                    f.op = VOP_GETGF;
                    f.a = nx.a;
                    f.b = nx.k;
                    f.k = in.k;
                    out.push_back(f);
                    map[i] = (int)out.size() - 1;
                    map[i + 1] = (int)out.size() - 1;
                    i += 2;
                    fused = true;
                }
            } else if (in.op == VOP_SELF && nx.op == VOP_CALL &&
                       nx.a == in.a && nx.b >= 1) {
                VInstr f;
                f.op = VOP_SCALL;
                f.a = in.a;
                f.b = in.b;
                f.k = in.k;
                f.c = nx.c;
                f.s = nx.b;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_MOVE && nx.op == VOP_RET &&
                       nx.a == in.a && nx.b == 1) {
                VInstr f;
                f.op = VOP_RET;
                f.a = in.b;
                f.b = 1;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_LOADK && nx.op == VOP_RET &&
                       nx.a == in.a && nx.b == 1) {
                VInstr f;
                f.op = VOP_RETK;
                f.a = in.a;
                f.k = in.k;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_LOADK && nx.op == VOP_SETT_K &&
                       nx.a == in.a) {
                VInstr f;
                f.op = VOP_TSETK;
                f.a = nx.b;
                f.b = in.k;
                f.k = nx.k;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_MOVE && nx.op == VOP_SETT_K &&
                       nx.a == in.a) {
                VInstr f;
                f.op = VOP_MVSETK;
                f.a = nx.b;
                f.b = in.b;
                f.k = nx.k;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op == VOP_GETT_K && nx.op == VOP_GETT_K &&
                       nx.a == in.a + 1 && nx.b == in.b && in.b != in.a) {
                VInstr f;
                f.op = VOP_TGET2;
                f.a = in.a;
                f.b = in.k;
                f.c = in.b;
                f.k = nx.k;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (in.op >= VOP_ADDK && in.op <= VOP_POWK &&
                       nx.op >= VOP_ADDK && nx.op <= VOP_POWK &&
                       nx.b == in.a &&
                       (noLive || in.a == nx.a || regDeadAfter(p, i + 2, in.a))) {

                auto kop6 = [](int op) -> int {
                    switch (op) {
                        case VOP_ADDK: return 0;
                        case VOP_SUBK: return 1;
                        case VOP_MULK: return 2;
                        case VOP_DIVK: return 3;
                        case VOP_MODK: return 4;
                        default: return 5;
                    }
                };
                int o1 = kop6(in.op);
                int o2 = kop6(nx.op);
                VInstr f;
                f.op = VOP_KARITH;
                f.a = nx.a;
                f.b = in.k;
                f.c = in.b;
                f.k = nx.k;
                f.s = o1 * 6 + o2 + 1;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (!noTgetc &&
                       in.op == VOP_GETT_K && nx.op == VOP_GETT_K &&
                       nx.b == in.a &&
                       (nx.a == in.a || regDeadAfter(p, i + 2, in.a))) {

                VInstr f;
                f.op = VOP_TGETC;
                f.a = nx.a;
                f.b = in.k;
                f.c = in.b;
                f.k = nx.k;
                out.push_back(f);
                map[i] = (int)out.size() - 1;
                map[i + 1] = (int)out.size() - 1;
                i += 2;
                fused = true;
            } else if (!noTaddk &&
                       in.op == VOP_GETT_K &&
                       ((nx.op >= VOP_ADDK && nx.op <= VOP_POWK) ||
                        nx.op == VOP_RSUBK || nx.op == VOP_RDIVK ||
                        nx.op == VOP_RPOWK || nx.op == VOP_ADDI ||
                        nx.op == VOP_SUBI || nx.op == VOP_MULI) &&
                       nx.b == in.a &&
                       (nx.a == in.a || regDeadAfter(p, i + 2, in.a))) {

                int sel = 0;
                VConst kc;
                switch (nx.op) {
                    case VOP_ADDK: sel = 1; break;
                    case VOP_SUBK: sel = 2; break;
                    case VOP_MULK: sel = 3; break;
                    case VOP_DIVK: sel = 4; break;
                    case VOP_MODK: sel = 5; break;
                    case VOP_POWK: sel = 6; break;
                    case VOP_RSUBK: sel = 7; break;
                    case VOP_RDIVK: sel = 8; break;
                    case VOP_RPOWK: sel = 9; break;
                    case VOP_ADDI: case VOP_MULI:
                    case VOP_SUBI: {
                        sel = nx.op == VOP_ADDI ? 1 : nx.op == VOP_SUBI ? 2 : 3;
                        kc.t = VConst::NUM;
                        kc.n = (double)nx.s;
                        break;
                    }
                    default:
                        sel = 0;
                        break;
                }
                if (sel == 0) {
                    out.push_back(in);
                    map[i] = (int)out.size() - 1;
                    i += 1;
                    fused = true;
                } else {
                    if (kc.t == VConst::NUM) {
                        p.ks.push_back(kc);
                    }
                    VInstr f;
                    f.op = VOP_TADDK;
                    f.a = nx.a;
                    f.b = in.k;
                    f.c = in.b;
                    f.k = nx.k;
                    f.s = sel;
                    if (kc.t == VConst::NUM) f.k = (int)p.ks.size();
                    out.push_back(f);
                    map[i] = (int)out.size() - 1;
                    map[i + 1] = (int)out.size() - 1;
                    i += 2;
                    fused = true;
                }
            }
        }
        if (!fused) {
            out.push_back(in);
            map[i] = (int)out.size() - 1;
            i += 1;
        }
    }
    for (auto& in : out) {
        if (in.jump && in.target >= 0 && in.target < (int)map.size() && map[in.target] >= 0) {
            in.target = map[in.target];
        }
    }
    p.code = std::move(out);
}

std::vector<char> hotRanges(const VProto& p) {
    std::vector<char> hot(p.code.size(), 0);
    for (size_t i = 0; i < p.code.size(); ++i) {
        const VInstr& in = p.code[i];
        if (in.jump && in.target >= 0 && in.target <= (int)i) {
            for (int t = in.target; t <= (int)i; ++t) hot[t] = 1;
        }
    }
    return hot;
}

void passOpaqueProto(VProto& p, Rng& rng, double chance) {
    std::vector<char> hot = hotRanges(p);
    std::vector<VInstr> out;
    std::vector<int> map(p.code.size(), -1);

    std::vector<std::pair<int, int>> probeFix;
    int jbase = (int)rng.range(3);
    int s1 = p.nregs + 1 + jbase;
    int s2 = s1 + 1;
    int s3 = s1 + 2;
    p.nregs += 3 + jbase;
    for (size_t i = 0; i < p.code.size(); ++i) {
        if (rng.chance(chance) && !hot[i]) {
            int k = 2 + (int)rng.range(999);

            int variant = (int)rng.range(12);
            if (std::getenv("EXF_NO_V67")) variant %= 6;
            if (variant >= 10) {
                VInstr l1;
                l1.op = VOP_LOADINT;
                l1.a = s1;
                l1.s = k;
                out.push_back(l1);
                VInstr l2b;
                l2b.op = VOP_LOADINT;
                l2b.a = s2;
                l2b.s = k;
                out.push_back(l2b);
                VInstr l3;
                l3.op = VOP_LOADTRUE;
                l3.a = s3;
                out.push_back(l3);
                int prIdxF = (int)out.size();
                VInstr prF;
                prF.op = variant == 10 ? VOP_JIFT : VOP_JIFF;
                prF.a = s3;
                prF.jump = true;
                out.push_back(prF);
                int nj = 3 + (int)rng.range(6);
                for (int j = 0; j < nj; ++j) {
                    VInstr jn;
                    int sel = (int)rng.range(8);
                    if (sel == 0) {
                        jn.op = VOP_ADD;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 1) {
                        jn.op = VOP_SUB;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 2) {
                        jn.op = (int)(VOP_DECOY0 + rng.range(100));
                        jn.a = s3;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 3) {
                        jn.op = VOP_MOVE;
                        jn.a = s2;
                        jn.b = s1;
                    } else if (sel == 4) {
                        jn.op = VOP_MUL;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 5) {
                        jn.op = VOP_DIV;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 6) {
                        jn.op = VOP_MOD;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else {
                        jn.op = VOP_CONCAT2;
                        jn.a = s3;
                        jn.b = s2;
                        jn.c = s1;
                    }
                    out.push_back(jn);
                }
                int contIdF = (int)out.size();
                out.push_back(p.code[i]);
                map[i] = contIdF;
                out[(size_t)prIdxF].target = contIdF;
                out[(size_t)prIdxF].jump = true;
                probeFix.push_back({prIdxF, contIdF});
                continue;
            }
            if (variant >= 6) {
                VInstr l1;
                l1.op = VOP_LOADINT;
                l1.a = s1;
                l1.s = k;
                out.push_back(l1);

                VInstr l2b;
                l2b.op = VOP_LOADINT;
                l2b.a = s2;
                l2b.s = k;
                out.push_back(l2b);
                VInstr l3b;
                l3b.op = VOP_LOADINT;
                l3b.a = s3;
                l3b.s = 0;
                out.push_back(l3b);
                VConst kc;
                kc.t = VConst::NUM;
                kc.n = (double)k;
                p.ks.push_back(kc);
                int prIdx6 = (int)out.size();
                VInstr pr6;
                pr6.op = variant == 6 ? VOP_IFEK
                       : variant == 7 ? VOP_IFNK
                       : variant == 8 ? VOP_IFLEK
                                      : VOP_IFLTK;
                pr6.a = s1;
                pr6.b = 0;
                pr6.k = (int)p.ks.size();
                pr6.jump = true;
                out.push_back(pr6);
                int nj = 3 + (int)rng.range(6);
                for (int j = 0; j < nj; ++j) {
                    VInstr jn;

                    int sel = (int)rng.range(8);
                    if (sel == 0) {
                        jn.op = VOP_ADD;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 1) {
                        jn.op = VOP_SUB;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 2) {
                        jn.op = (int)(VOP_DECOY0 + rng.range(100));
                        jn.a = s3;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 3) {
                        jn.op = VOP_MOVE;
                        jn.a = s2;
                        jn.b = s1;
                    } else if (sel == 4) {
                        jn.op = VOP_MUL;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 5) {
                        jn.op = VOP_DIV;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else if (sel == 6) {
                        jn.op = VOP_MOD;
                        jn.a = s2;
                        jn.b = s2;
                        jn.c = s1;
                    } else {
                        jn.op = VOP_CONCAT2;
                        jn.a = s3;
                        jn.b = s2;
                        jn.c = s1;
                    }
                    out.push_back(jn);
                }
                int contId6 = (int)out.size();
                out.push_back(p.code[i]);
                map[i] = contId6;
                out[(size_t)prIdx6].target = contId6;
                out[(size_t)prIdx6].jump = true;
                probeFix.push_back({prIdx6, contId6});
                continue;
            }
            VInstr l1;
            l1.op = VOP_LOADINT;
            l1.a = s1;
            l1.s = k;
            out.push_back(l1);
            VInstr l2;
            l2.op = VOP_LOADINT;
            l2.a = s2;
            l2.s = k;
            out.push_back(l2);
            VInstr mu;
            mu.op = variant == 1 ? VOP_SUB
                    : variant == 2 ? VOP_ADD
                    : variant == 3 ? VOP_UNM
                    : variant == 4 ? VOP_DIV
                    : variant == 5 ? VOP_MOD
                                   : VOP_MUL;
            mu.a = s2;
            mu.b = s2;
            mu.c = s1;
            out.push_back(mu);
            VInstr l3;
            l3.op = VOP_LOADINT;
            l3.a = s3;
            l3.s = 0;
            out.push_back(l3);
            int prIdx = (int)out.size();
            VInstr pr;
            pr.op = (variant == 1 || variant == 5) ? VOP_IFEQ
                    : (variant == 2 || variant == 4) ? VOP_IFGT
                                                     : VOP_IFLT;
            pr.a = variant == 2 ? s1 : s2;
            pr.b = variant == 2 ? s2 : (variant == 5 ? s3 : s1);
            pr.jump = true;
            out.push_back(pr);
            int nj = 3 + (int)rng.range(6);
            for (int j = 0; j < nj; ++j) {
                VInstr jn;
                int sel = (int)rng.range(8);
                if (sel == 0) {
                    jn.op = VOP_ADD;
                    jn.a = s2;
                    jn.b = s2;
                    jn.c = s1;
                } else if (sel == 1) {
                    jn.op = VOP_SUB;
                    jn.a = s2;
                    jn.b = s2;
                    jn.c = s1;
                } else if (sel == 2) {
                    jn.op = (int)(VOP_DECOY0 + rng.range(100));
                    jn.a = s3;
                    jn.b = s2;
                    jn.c = s1;
                } else if (sel == 3) {
                    jn.op = VOP_MOVE;
                    jn.a = s2;
                    jn.b = s1;
                } else if (sel == 4) {
                    jn.op = VOP_MUL;
                    jn.a = s2;
                    jn.b = s2;
                    jn.c = s1;
                } else if (sel == 5) {
                    jn.op = VOP_DIV;
                    jn.a = s2;
                    jn.b = s2;
                    jn.c = s1;
                } else if (sel == 6) {
                    jn.op = VOP_MOD;
                    jn.a = s2;
                    jn.b = s2;
                    jn.c = s1;
                } else {
                    jn.op = VOP_CONCAT2;
                    jn.a = s3;
                    jn.b = s2;
                    jn.c = s1;
                }
                out.push_back(jn);
            }
            int contId = (int)out.size();
            out.push_back(p.code[i]);
            map[i] = contId;
            out[prIdx].target = contId;
            out[prIdx].jump = true;
            probeFix.push_back({prIdx, contId});
            continue;
        }
        map[i] = (int)out.size();
        out.push_back(p.code[i]);
    }
    for (auto& in : out)
        if (in.jump && in.target >= 0 && in.target < (int)map.size() && map[in.target] >= 0)
            in.target = map[in.target];
    for (const auto& pf : probeFix)
        out[(size_t)pf.first].target = pf.second;
    p.code = std::move(out);
}

void passDecoyProto(VProto& p, Rng& rng, double chance) {
    std::vector<char> hot = hotRanges(p);
    std::vector<VInstr> out;
    std::vector<int> map(p.code.size(), -1);
    int dbase = (int)rng.range(3);
    int s1 = p.nregs + 1 + dbase;
    int s2 = s1 + 1;
    p.nregs += 2 + dbase;
    for (size_t i = 0; i < p.code.size(); ++i) {
        map[i] = (int)out.size();
        out.push_back(p.code[i]);
        if (rng.chance(chance) && !hot[i]) {
            VInstr d;
            d.op = (int)(VOP_DECOY0 + rng.range(100));
            d.a = s1;
            d.b = s2;
            d.c = s1;
            out.push_back(d);
            if (rng.chance(0.5)) {
                VInstr d2;
                d2.op = VOP_MOVE;
                d2.a = s2;
                d2.b = s1;
                out.push_back(d2);
            }
        }
    }
    for (auto& in : out)
        if (in.jump && in.target >= 0 && in.target < (int)map.size() && map[in.target] >= 0)
            in.target = map[in.target];
    p.code = std::move(out);
}

void passRegRandProto(VProto& p, Rng& rng, int regBaseMax) {
    int base = regBaseMax > 0 ? 1 + (int)rng.range((std::uint64_t)regBaseMax) : 0;
    int pad = (int)rng.range(5);
    for (auto& in : p.code) {
        in.a += base;
        if (in.op == VOP_SCALL || in.op == VOP_MCALL || in.op == VOP_MTAIL ||
            in.op == VOP_SCT) {
            in.b += base;
            continue;
        }

        if (in.op == VOP_TGET2 || in.op == VOP_KARITH ||
            in.op == VOP_TGETC || in.op == VOP_TADDK) {
            in.c += base;
            continue;
        }
        if (onlyAReg(in.op)) continue;
        if (isCountB(in.op)) continue;
        in.b += base;
        if (in.op == VOP_TFOR) continue;
        in.c += base;
        if ((in.op == VOP_ADD || in.op == VOP_MUL) && rng.chance(0.5)) {
            std::swap(in.b, in.c);
        } else if ((in.op == VOP_IFEQ || in.op == VOP_IFNE) && rng.chance(0.5)) {
            std::swap(in.a, in.b);
        }
    }
    p.nregs += base + pad;
    p.regBase = base;
}

void passThreadProto(VProto& p) {
    for (size_t i = 0; i < p.code.size(); ++i) {
        VInstr& in = p.code[i];
        if (!in.jump || in.target < 0 || in.op == VOP_FORPREP ||
            in.op == VOP_FORLOOP || in.op == VOP_TFOR ||
            in.op == VOP_FORPREP1 || in.op == VOP_FORLOOP1) continue;
        int t = in.target;
        int guard = 0;
        while (t >= 0 && t < (int)p.code.size() && guard < 64) {
            const VInstr& tj = p.code[(size_t)t];
            if (tj.op != VOP_JMP || !tj.jump || tj.target < 0 || tj.target == t) break;
            t = tj.target;
            ++guard;
        }
        if (t != in.target) in.target = t;
    }
}

void passShuffleProto(VProto& p, Rng& rng) {
    std::vector<BlockInfo> blocks = blockify(p);
    if (blocks.size() < 2) return;
    std::vector<int> tmap;
    normalizeFallthroughs(p, blocks, tmap);
    size_t nb = blocks.size();
    std::vector<size_t> order;
    for (size_t i = 0; i < nb; ++i) order.push_back(i);
    for (size_t i = nb - 1; i > 0; --i) {
        size_t j = (size_t)rng.range(i + 1);
        std::swap(order[i], order[j]);
    }
    size_t entryPos = 0;
    for (size_t i = 0; i < nb; ++i) {
        if (order[i] == 0) {
            entryPos = i;
            break;
        }
    }
    std::swap(order[0], order[entryPos]);
    std::vector<VInstr> out;
    std::vector<int> finalMap((size_t)p.code.size(), -1);
    for (size_t oi : order) {
        BlockInfo& b = blocks[oi];
        b.newStart = (int)out.size();
        for (int i = b.start; i <= b.end; ++i) {
            finalMap[i] = (int)out.size();
            out.push_back(p.code[i]);
        }
    }
    for (auto& in : out) {
        if (in.jump && in.target >= 0 && in.target < (int)finalMap.size() &&
            finalMap[in.target] >= 0) {
            in.target = finalMap[in.target];
        }
    }
    p.code = std::move(out);
}

bool passFlattenProto(VProto& p, Rng& rng) {
    std::vector<BlockInfo> blocks = blockify(p);
    if (blocks.size() < 3) return false;
    size_t nb = blocks.size();
    std::vector<int> tmap;
    normalizeFallthroughs(p, blocks, tmap);
    auto blkOf = [&](int normPos) -> int {
        for (size_t bi = 0; bi < nb; ++bi)
            if (blocks[bi].start == normPos) return (int)bi;
        return -1;
    };
    std::vector<char> hot = hotRanges(p);
    std::vector<char> nat(nb, 0);
    size_t nDisp = 0;
    for (size_t bi = 0; bi < nb; ++bi) {
        for (int i = blocks[bi].start; i <= blocks[bi].end; ++i)
            if (hot[(size_t)i]) nat[bi] = 1;
        if (!nat[bi]) ++nDisp;
    }
    if (nDisp < 2) return false;
    std::vector<int> symKind((size_t)p.code.size(), 0);
    std::vector<int> symT((size_t)p.code.size(), -1);
    std::vector<int> symF((size_t)p.code.size(), -1);
    for (size_t bi = 0; bi < nb; ++bi) {
        if (nat[bi]) {
            for (int i = blocks[bi].start; i <= blocks[bi].end; ++i)
                if (p.code[(size_t)i].jump) symKind[(size_t)i] = 3;
            continue;
        }
        int lastPos = blocks[bi].end;
        int firstPos = blocks[bi].start;
        VInstr& in = p.code[(size_t)lastPos];
        if (lastPos - 1 >= firstPos) {
            VInstr& prev = p.code[(size_t)(lastPos - 1)];
            if (in.op == VOP_JMP && prev.jump &&
                prev.op != VOP_JMP && prev.op != VOP_FORPREP &&
                prev.op != VOP_FORLOOP && prev.op != VOP_TFOR &&
                prev.op != VOP_FORPREP1 && prev.op != VOP_FORLOOP1) {
                int tp = blkOf(prev.target);
                if (tp >= 0) {
                    int fb = blocks[bi].fallBlk;

                    int jp = blkOf(in.target);
                    symKind[(size_t)(lastPos - 1)] = 2;
                    symT[(size_t)(lastPos - 1)] = tp;
                    symF[(size_t)(lastPos - 1)] = fb >= 0 ? fb : jp;
                    symKind[lastPos] = 1;
                    symT[lastPos] = fb >= 0 ? fb : jp;
                    continue;
                }
            }
        }
        if (!in.jump) continue;
        if (in.op == VOP_FORPREP || in.op == VOP_FORLOOP || in.op == VOP_TFOR ||
            in.op == VOP_FORPREP1 || in.op == VOP_FORLOOP1) continue;
        int tb = blkOf(in.target);
        if (tb < 0) {
            symKind[lastPos] = 3;
            continue;
        }
        if (in.op == VOP_JMP) {
            symKind[lastPos] = 1;
            symT[lastPos] = tb;
        } else {
            symKind[lastPos] = 2;
            symT[lastPos] = tb;
            symF[lastPos] = blocks[bi].fallBlk;
        }
    }
    int nEdges = 0;
    std::vector<char> isTgt(nb, 0);
    for (size_t i = 0; i < p.code.size(); ++i) {
        if (symKind[i] == 1 && symT[i] >= 0) {
            isTgt[(size_t)symT[i]] = 1;
            ++nEdges;
        } else if (symKind[i] == 2) {
            if (symT[i] >= 0) {
                isTgt[(size_t)symT[i]] = 1;
                ++nEdges;
            }
            if (symF[i] >= 0) {
                isTgt[(size_t)symF[i]] = 1;
                ++nEdges;
            }
        }
    }
    if (nEdges == 0) return false;
    std::vector<int> cand;
    for (size_t bi = 0; bi < nb; ++bi)
        if (isTgt[bi]) cand.push_back((int)bi);
    for (size_t i = cand.size() - 1; i > 0; --i) {
        size_t j = (size_t)rng.range(i + 1);
        std::swap(cand[i], cand[j]);
    }
    size_t ndec = 2 + (size_t)rng.range(8);
    size_t nhop = 0;
    if (cand.size() >= 3 && nEdges >= 4) nhop = 2 + (size_t)rng.range(7);
    if (nhop > cand.size()) nhop = cand.size();
    std::vector<int> hopOf(nb, -1);
    for (size_t j = 0; j < nhop; ++j) hopOf[(size_t)cand[j]] = (int)j;
    size_t total = nb + nhop + ndec;
    std::uint64_t MA = 23 + 2 * (std::uint64_t)rng.range(478);
    std::uint64_t MB = 1 + (std::uint64_t)rng.range(4093);
    if ((std::uint64_t)total * MA + MB > 8388600ULL) {
        MA = (8388600ULL - MB) / (std::uint64_t)total;
        if (MA % 2 == 0) MA -= 1;
        if (MA < 3 || (std::uint64_t)total * MA + MB > 8388600ULL) MA = 0;
    }
    std::unordered_set<int> usedTok;
    std::unordered_map<std::uint64_t, int> tokMemo;
    auto tok = [&](std::uint64_t id) -> int {
        auto it = tokMemo.find(id);
        if (it != tokMemo.end()) return it->second;
        std::uint64_t base = id * (std::uint64_t)MA + (std::uint64_t)MB;
        std::uint32_t mk = mixIdx(1400003ull + base * 3ull, id * 2ull + 1ull);
        mk = lehmer(mk);
        mk = lehmer(mk);
        mk = lehmer(mk);
        int val = 100000 + (int)(mk % 8000000ull);
        while (usedTok.count(val)) {
            mk = lehmer(mk);
            val = 100000 + (int)(mk % 8000000ull);
        }
        usedTok.insert(val);
        tokMemo.emplace(id, val);
        return val;
    };
    std::vector<int> ids(total);
    for (size_t i = 0; i < total; ++i) ids[i] = (int)i + 1;
    for (size_t i = total - 1; i > 0; --i) {
        size_t j = (size_t)rng.range(i + 1);
        std::swap(ids[i], ids[j]);
    }
    std::vector<size_t> order;
    for (size_t i = 0; i < nb; ++i) order.push_back(i);
    for (size_t i = nb - 1; i > 0; --i) {
        size_t j = (size_t)rng.range(i + 1);
        std::swap(order[i], order[j]);
    }
    size_t entryPos = 0;
    for (size_t i = 0; i < nb; ++i) {
        if (order[i] == 0) {
            entryPos = i;
            break;
        }
    }
    std::swap(order[0], order[entryPos]);
    int Rs = p.nregs + 1;
    p.nregs += 2;
    std::vector<int> state(nb, 0);
    std::vector<int> hopState(nhop, 0);
    std::vector<int> decState(ndec, 0);
    for (size_t bi = 0; bi < nb; ++bi) state[bi] = ids[bi];
    for (size_t j = 0; j < nhop; ++j) hopState[j] = ids[nb + j];
    for (size_t di = 0; di < ndec; ++di) decState[di] = ids[nb + nhop + di];
    std::vector<VInstr> out;
    std::vector<int> finalMap((size_t)p.code.size(), -1);
    std::vector<int> emittedOld;
    std::vector<int> c1Positions;
    auto emitInstr = [&](int normPos, const VInstr& in) {
        finalMap[normPos] = (int)out.size();
        emittedOld.push_back(normPos);
        out.push_back(in);
    };
    auto emitLD = [&](int tv) -> int {
        int pos = (int)out.size();
        VInstr sj;
        sj.op = VOP_STATEJMP;
        sj.a = Rs;
        sj.s = tv;
        out.push_back(sj);
        emittedOld.push_back(-1);
        return pos;
    };
    auto edgeTok = [&](int t) -> int {
        if (t < 0 || t >= (int)nb) return tok((std::uint64_t)state[0]);
        int h = hopOf[(size_t)t];
        return tok(h >= 0 ? (std::uint64_t)hopState[(size_t)h]
                          : (std::uint64_t)state[(size_t)t]);
    };
    for (size_t k = 0; k < nb; ++k) {
        size_t bi = order[k];
        BlockInfo& b = blocks[bi];
        b.newStart = (int)out.size();
        for (int i = b.start; i <= b.end; ++i) {
            int sk = symKind[i];
            if (sk == 0 || sk == 3) {
                emitInstr(i, p.code[i]);
            } else if (sk == 1) {
                finalMap[i] = emitLD(edgeTok(symT[i]));
            } else {
                int cur = (int)out.size();
                VInstr c1 = p.code[i];
                c1.jump = true;
                c1.target = cur + 2;
                c1Positions.push_back(cur);
                emitInstr(i, c1);
                int fb = symF[i];
                emitLD(edgeTok(fb >= 0 ? fb : symT[i]));
                emitLD(edgeTok(symT[i]));
            }
        }
        p.flat.push_back({tok((std::uint64_t)state[bi]), blocks[bi].newStart});
    }
    VInstr pro1;
    pro1.op = VOP_STATEJMP;
    pro1.a = Rs;
    pro1.s = tok((std::uint64_t)state[0]);
    out.insert(out.begin(), pro1);
    emittedOld.insert(emittedOld.begin(), -1);
    for (int cp : c1Positions) out[(size_t)(cp + 1)].target += 1;
    for (auto& fm : finalMap)
        if (fm >= 0) fm += 1;
    for (size_t bi = 0; bi < nb; ++bi) blocks[bi].newStart += 1;
    for (auto& f : p.flat) f.second += 1;
    for (size_t k = 0; k < out.size(); ++k) {
        VInstr& in = out[k];
        if (!in.jump || in.target < 0) continue;
        int oldPos = k < emittedOld.size() ? emittedOld[k] : -1;
        bool keepSym = oldPos >= 0 && symKind[oldPos] == 2;
        if (keepSym) continue;
        if (in.op == VOP_FORPREP || in.op == VOP_FORLOOP || in.op == VOP_TFOR ||
            in.op == VOP_FORPREP1 || in.op == VOP_FORLOOP1 ||
            (oldPos >= 0 && symKind[oldPos] == 3)) {
            if (in.target < (int)finalMap.size() && finalMap[in.target] >= 0) {
                in.target = finalMap[in.target];
            }
        }
    }
    for (size_t j = 0; j < nhop; ++j) {
        int hStart = (int)out.size();
        VInstr sj2;
        sj2.op = VOP_STATEJMP;
        sj2.a = Rs;
        sj2.s = tok((std::uint64_t)state[(size_t)cand[j]]);
        out.push_back(sj2);
        p.flat.push_back({tok((std::uint64_t)hopState[j]), hStart});
    }
    for (size_t di = 0; di < ndec; ++di) {
        int dStart = (int)out.size();
        VInstr l1;
        l1.op = VOP_LOADINT;
        l1.a = Rs;
        l1.s = (int)rng.range(1000);
        out.push_back(l1);
        VInstr dd;
        dd.op = (int)(VOP_DECOY0 + rng.range(100));
        dd.a = Rs;
        out.push_back(dd);
        VInstr rt;
        rt.op = VOP_RET;
        rt.a = 0;
        rt.b = 1;
        out.push_back(rt);
        p.flat.push_back({tok((std::uint64_t)decState[di]), dStart});
    }
    p.code = std::move(out);
    p.flattened = true;
    return true;
}

}

void runVmPasses(VmIR& ir, std::uint64_t seed, const VmOptions& opt) {
    Rng rng(seed ^ 0x5A5A57A1ULL);
    const char* dbg = std::getenv("EXF_PASSES");
    std::string on = dbg ? dbg : "branch,fuse,arith,opaque,decoy,flatten,shuffle,thread";
    auto has = [&](const std::string& t) {
        return on.find(t) != std::string::npos;
    };
    std::vector<int> parentOf(ir.protos.size(), -1);
    for (size_t pi = 0; pi < ir.protos.size(); ++pi)
        for (int ch : ir.protos[pi].children)
            if (ch >= 0 && ch < (int)ir.protos.size()) parentOf[ch] = (int)pi;
    for (auto& p : ir.protos) {
        if (std::getenv("EXF_NRDBG")) std::cerr << "NR start " << p.nregs << "\n";
        if (opt.branchChance > 0 && has("branch"))
            passBranchXformProto(p, rng, opt.branchChance);
        if (opt.fuseChance > 0 && has("fuse"))
            passFuseProto(p, rng, opt.fuseChance);
        if (opt.arithChance > 0 && has("arith"))
            passArithProto(p, rng, opt.arithChance);
        if (opt.opaqueChance > 0 && has("opaque"))
            passOpaqueProto(p, rng, opt.opaqueChance);
        if (opt.decoyChance > 0 && has("decoy"))
            passDecoyProto(p, rng, opt.decoyChance);
        passRegRandProto(p, rng, opt.regBaseMax);
        if (std::getenv("EXF_NRDBG")) std::cerr << "NR end " << p.nregs << "\n";
        bool flattened = false;
        if (opt.flattenChance > 0 && has("flatten") &&
            rng.chance(opt.flattenChance)) {
            flattened = passFlattenProto(p, rng);
        }
        if (!flattened && opt.shuffleBlocks && has("shuffle")) {
            passShuffleProto(p, rng);
        }
        if (has("thread")) passThreadProto(p);
    }
    for (size_t pi = 0; pi < ir.protos.size(); ++pi) {
        int par = parentOf[pi];
        if (par < 0) continue;
        for (auto& u : ir.protos[pi].upvals)
            if (u.kind == 0) u.idx += ir.protos[par].regBase;
    }
}

namespace {

const char* opName(int op) {
    static const char* names[] = {
        "MOVE", "LOADNIL", "LOADTRUE", "LOADFALSE", "LOADINT", "LOADK",
        "GETGLOBAL", "SETGLOBAL", "GETUPVAL", "SETUPVAL",
        "GETT", "GETT_K", "SETT", "SETT_K", "NEWTABLE", "SETLIST", "SELF", "CONCAT",
        "ADD", "SUB", "MUL", "DIV", "MOD", "POW",
        "ADDK", "SUBK", "MULK", "DIVK", "MODK", "POWK",
        "UNM", "NOT", "LEN",
        "JMP", "IFEQ", "IFNE", "IFLT", "IFLE", "IFGT", "IFGE", "JIFF", "JIFT",
        "IFEK", "IFNK", "FLEQ", "FLNE", "FLLT", "FLLE", "FLGT", "FLGE",
        "CALL", "CALLM", "TAILCALL", "RET", "RETM", "VARARG", "VARARG1", "SPILL",
        "CLOSURE", "CLOSE",
        "FORPREP", "FORLOOP", "TFOR",
        "DISPATCH",
        "GETGF", "SCALL", "RETK",
        "MCALL", "GCALL", "MTAIL", "GTAIL", "KRET", "CRET",
        "SCT", "CRTM",
        "TSETK", "TGET2", "KARITH", "MVSETK",
        "RSUBK", "RDIVK", "RPOWK",
        "ADDI", "SUBI", "MULI",
        "IFLTK", "IFLEK", "IFGTK", "IFGEK",
        "IFKLT", "IFKLE", "IFKGT", "IFKGE",
        "CALL1", "CALL2", "CALL3",
        "RET0", "RET1",
        "GETTK", "GETTRK", "SETTRK",
        "NEWTAB_LIST",
        "LOAD2K", "MOVE2",
        "CONCAT2", "CONCAT3", "CONCATK",
        "GETT_I", "SETT_I",
        "FORPREP1", "FORLOOP1", "STATEJMP",
        "TGETC", "TADDK"
    };
    if (op >= VOP_DECOY0 && op < VOP_COUNT) {
        static char dn[16];
        std::snprintf(dn, sizeof(dn), "DECOY%d", op - VOP_DECOY0);
        return dn;
    }
    int nreal = VOP_DECOY0;
    return op >= 0 && op < nreal ? names[op] : "?";
}

}

void dumpVmIR(const VmIR& ir, std::ostream& os) {
    for (size_t pi = 0; pi < ir.protos.size(); ++pi) {
        const VProto& p = ir.protos[pi];
        os << "== proto " << pi << " params=" << p.nparams
           << " vararg=" << (p.vararg ? 1 : 0)
           << " nregs=" << p.nregs << "\n";
        for (size_t ui = 0; ui < p.upvals.size(); ++ui)
            os << "  upval[" << (ui + 1) << "] kind=" << p.upvals[ui].kind
               << " idx=" << p.upvals[ui].idx << "\n";
        for (size_t ki = 0; ki < p.ks.size(); ++ki) {
            const VConst& c = p.ks[ki];
            os << "  k[" << (ki + 1) << "] ";
            switch (c.t) {
                case VConst::NIL: os << "nil"; break;
                case VConst::BOOL: os << (c.b ? "true" : "false"); break;
                case VConst::NUM: os << "num " << c.n; break;
                case VConst::STR: os << "str \"" << c.s << "\""; break;
            }
            os << "\n";
        }
        for (size_t ii = 0; ii < p.code.size(); ++ii) {
            const VInstr& in = p.code[ii];
            os << "  [" << ii << "] " << opName(in.op)
               << " a=" << in.a << " b=" << in.b << " c=" << in.c
               << " s=" << in.s << " k=" << in.k;
            if (in.jump && in.target >= 0) os << " -> " << in.target;
            os << "\n";
        }
        os << "  children:";
        for (int ch : p.children) os << " " << ch;
        os << "\n";
        os << "  flat:";
        for (size_t fi = 0; fi < p.flat.size(); ++fi)
            os << " " << p.flat[fi].first << "->" << p.flat[fi].second;
        os << "\n";
    }
}

}
}
