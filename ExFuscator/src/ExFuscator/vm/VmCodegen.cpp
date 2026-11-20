/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#include "astra/vm/VmCodegen.hpp"
#include "astra/Diagnostic.hpp"
#include <cstring>

#include <cmath>

namespace astra {
namespace vm {

namespace {

constexpr int kMaxS24 = 8388607;
constexpr int kFlushFields = 24;
constexpr int kMaxConcat = 200;

struct CBScope {
    int baseSlot = 1;
    int hiddenSlots = 0;
    std::vector<std::pair<std::string, int>> vars;
    bool captured = false;
    bool isLoop = false;
    int loopKind = 0;
    std::vector<int> breakPatches;
    std::vector<int> contPatches;
    int contTarget = -1;
    int contKind = 0;
};

struct FG {
    VProto* p = nullptr;
    int pid = -1;
    FG* parent = nullptr;
    std::vector<CBScope> scopes;
    int freereg = 1;
    int maxreg = 1;
    bool usesUpvals = false;
};

bool isNumExpr(ast::Expr* e, double& out) {
    if (!e || e->kind != ast::EK::Num) return false;
    out = std::atof(e->text.c_str());
    return true;
}

bool isStrExpr(ast::Expr* e, const std::string*& out) {
    if (!e || e->kind != ast::EK::Str) return false;
    out = &e->text;
    return true;
}

class Compiler {
public:
    Compiler(ast::Chunk& chunk, std::uint64_t seed, const VmOptions& opt)
        : chunk_(chunk), rng_(seed ^ 0xA5A3B7ULL), opt_(opt) {}

    VmIR run() {
        FG rootFg;
        rootFg.p = addProto();
        rootFg.pid = 0;
        rootFg.parent = nullptr;
        rootFg.p->vararg = true;
        cur_ = &rootFg;
        CBScope fnScope;
        fnScope.baseSlot = 1;
        cur_->scopes.push_back(fnScope);
        compileBlock(chunk_.root);
        finishFunction();
        ir_.entry = 0;
        return std::move(ir_);
    }

private:
    ast::Chunk& chunk_;
    Rng rng_;
    VmOptions opt_;
    VmIR ir_;
    FG* cur_ = nullptr;
    std::vector<VProto*> byId_;

    VProto* addProto() {
        ir_.protos.emplace_back();
        byId_.push_back(&ir_.protos.back());
        return &ir_.protos.back();
    }

    VInstr& at(int id) { return cur_->p->code[(size_t)id]; }

    int here() const { return (int)cur_->p->code.size(); }

    int emit(const VInstr& in) {
        cur_->p->code.push_back(in);
        return (int)cur_->p->code.size() - 1;
    }

    int simple(int op, int a, int b = 0, int c = 0) {
        VInstr i;
        i.op = op;
        i.a = a;
        i.b = b;
        i.c = c;
        return emit(i);
    }

    int emitK(int op, int a, int b, int k) {
        VInstr i;
        i.op = op;
        i.a = a;
        i.b = b;
        i.k = k;
        return emit(i);
    }

    int emitJump(int op, int a, int b, int target) {
        VInstr i;
        i.op = op;
        i.a = a;
        i.b = b;
        i.target = target;
        i.jump = true;
        return emit(i);
    }

    int kStr(const std::string& s) {
        auto& ks = cur_->p->ks;
        for (size_t i = 0; i < ks.size(); ++i)
            if (ks[i].t == VConst::STR && ks[i].s == s) return (int)i + 1;
        VConst c;
        c.t = VConst::STR;
        c.s = s;
        ks.push_back(c);
        return (int)ks.size();
    }

    int kNum(double v) {
        auto& ks = cur_->p->ks;
        for (size_t i = 0; i < ks.size(); ++i)
            if (ks[i].t == VConst::NUM) {

                std::uint64_t a, b;
                std::memcpy(&a, &ks[i].n, 8);
                std::memcpy(&b, &v, 8);
                if (a == b) return (int)i + 1;
            }
        VConst c;
        c.t = VConst::NUM;
        c.n = v;
        ks.push_back(c);
        return (int)ks.size();
    }

    int kBool(bool b) {
        auto& ks = cur_->p->ks;
        VConst c;
        c.t = VConst::BOOL;
        c.b = b;
        ks.push_back(c);
        return (int)ks.size();
    }

    int kNil() {
        auto& ks = cur_->p->ks;
        VConst c;
        c.t = VConst::NIL;
        ks.push_back(c);
        return (int)ks.size();
    }

    int kIndexOf(ast::Expr* e) {
        if (!e) return kNil();
        switch (e->kind) {
            case ast::EK::Nil: return kNil();
            case ast::EK::True: return kBool(true);
            case ast::EK::False: return kBool(false);
            case ast::EK::Num: return kNum(std::atof(e->text.c_str()));
            case ast::EK::Str: return kStr(e->text);
            default: return kNil();
        }
    }

    static int kJumpBase(ast::SO cmp) {
        switch (cmp) {
            case ast::SO::Lt: return VOP_IFLTK;
            case ast::SO::Le: return VOP_IFLEK;
            case ast::SO::Gt: return VOP_IFGTK;
            case ast::SO::Ge: return VOP_IFGEK;
            case ast::SO::Eq: return VOP_IFEK;
            default: return VOP_IFNK;
        }
    }

    static int kJumpLeft(ast::SO cmp) {
        switch (cmp) {
            case ast::SO::Lt: return VOP_IFKLT;
            case ast::SO::Le: return VOP_IFKLE;
            case ast::SO::Gt: return VOP_IFKGT;
            case ast::SO::Ge: return VOP_IFKGE;
            case ast::SO::Eq: return VOP_IFEK;
            default: return VOP_IFNK;
        }
    }

    static bool smallInt(double& v) {
        return v == std::floor(v) && std::fabs(v) <= 8388607.0;
    }

    static constexpr int kMaxReg = 250;

    [[noreturn]] static void failReg() {
        throw AstraError(
            "function or expression too complex (register limit is 250)");
    }

    int reserve() {
        int r = cur_->freereg++;
        if (cur_->freereg > cur_->maxreg) cur_->maxreg = cur_->freereg;
        if (cur_->freereg > kMaxReg) failReg();
        return r;
    }

    int reserveN(int n) {
        int base = cur_->freereg;
        cur_->freereg += n;
        if (cur_->freereg > cur_->maxreg) cur_->maxreg = cur_->freereg;
        if (cur_->freereg > kMaxReg) failReg();
        return base;
    }

    void ensureFree(int slot) {
        if (slot >= cur_->freereg) cur_->freereg = slot + 1;
        if (cur_->freereg > cur_->maxreg) cur_->maxreg = cur_->freereg;
        if (cur_->freereg > kMaxReg) failReg();
    }

    void syncFreereg() {
        int used = 1;
        for (const CBScope& s : cur_->scopes) {
            used += (int)s.vars.size() + s.hiddenSlots;
            for (const auto& v : s.vars)
                if (v.second + 1 > used) used = v.second + 1;
            int end = s.baseSlot + s.hiddenSlots + (int)s.vars.size();
            if (end > used) used = end;
        }
        cur_->freereg = used;
    }

    int findLocal(FG* f, const std::string& n) {
        for (auto it = f->scopes.rbegin(); it != f->scopes.rend(); ++it)
            for (auto v = it->vars.rbegin(); v != it->vars.rend(); ++v)
                if (v->first == n) return v->second;
        return -1;
    }

    int addUpval(FG* f, int kind, int idx) {
        auto& uv = f->p->upvals;
        for (size_t i = 0; i < uv.size(); ++i)
            if (uv[i].kind == kind && uv[i].idx == idx) return (int)i + 1;

        if (uv.size() >= 200)
            throw AstraError("too many upvalues (limit is 200) in a function");
        VUpval u;
        u.kind = kind;
        u.idx = idx;
        uv.push_back(u);
        return (int)uv.size();
    }

    int resolveUpval(FG* f, const std::string& n) {
        if (!f->parent) return -1;
        int slot = findLocal(f->parent, n);
        if (slot >= 0) {
            f->parent->usesUpvals = true;
            for (auto& sc : f->parent->scopes)
                for (auto& v : sc.vars)
                    if (v.second == slot) sc.captured = true;
            return addUpval(f, 0, slot);
        }
        int ui = resolveUpval(f->parent, n);
        if (ui >= 0) return addUpval(f, 1, ui);
        return -1;
    }

    void compileBlock(ast::Block* b) {
        if (!b) return;
        for (ast::Stmt* st : b->stats) {
            compileStmt(st);
            syncFreereg();
        }
    }

    int newChild(int nparams, bool vararg) {
        VProto* cp = addProto();
        int pid = (int)byId_.size() - 1;
        cp->nparams = nparams;
        cp->vararg = vararg;
        cur_->p->children.push_back(pid);
        return pid;
    }

    void finishFunction() {
        VProto* p = cur_->p;
        bool lastIsTerm = false;
        if (!p->code.empty()) {
            int op = p->code.back().op;
            lastIsTerm = op == VOP_RET || op == VOP_RETM || op == VOP_TAILCALL ||
                         op == VOP_RET0 || op == VOP_RET1;
        }
        if (!lastIsTerm) simple(VOP_RET0, 0, 0);
        p->nregs = cur_->maxreg > cur_->freereg ? cur_->maxreg : cur_->freereg;
    }

    void enterScope(bool loop = false, int kind = 0) {
        CBScope s;
        s.baseSlot = cur_->freereg;
        s.isLoop = loop;
        s.loopKind = kind;
        cur_->scopes.push_back(s);
    }

    void exitScope() {
        CBScope s = cur_->scopes.back();
        cur_->scopes.pop_back();
        if (s.captured) simple(VOP_CLOSE, s.baseSlot);
        int endId = (int)cur_->p->code.size();
        for (int pid : s.breakPatches) at(pid).target = endId;
        syncFreereg();
    }

    CBScope* innermostLoop() {
        for (auto it = cur_->scopes.rbegin(); it != cur_->scopes.rend(); ++it)
            if (it->isLoop) return &*it;
        return nullptr;
    }

    void emitCloseIf(int baseSlot) {
        if (cur_->usesUpvals) simple(VOP_CLOSE, baseSlot);
    }

    bool constTruthy(ast::Expr* e) {
        if (!e) return false;
        switch (e->kind) {
            case ast::EK::Nil: return false;
            case ast::EK::False: return false;
            case ast::EK::True: return true;
            case ast::EK::Num: return std::atof(e->text.c_str()) != 0.0;
            case ast::EK::Str: return !e->text.empty();
            default: return false;
        }
    }

    bool isConstKind(ast::Expr* e) {
        if (!e) return true;
        switch (e->kind) {
            case ast::EK::Nil: case ast::EK::True: case ast::EK::False:
            case ast::EK::Num: case ast::EK::Str: return true;
            default: return false;
        }
    }

    void cConst(ast::Expr* e, int dst) {
        switch (e->kind) {
            case ast::EK::Nil: simple(VOP_LOADNIL, dst); break;
            case ast::EK::True: simple(VOP_LOADTRUE, dst); break;
            case ast::EK::False: simple(VOP_LOADFALSE, dst); break;
            case ast::EK::Num: {
                double v = std::atof(e->text.c_str());
                if (v == std::floor(v) && std::fabs(v) <= (double)kMaxS24) {
                    VInstr i;
                    i.op = VOP_LOADINT;
                    i.a = dst;
                    i.s = (std::int64_t)v;
                    emit(i);
                } else {
                    emitK(VOP_LOADK, dst, 0, kNum(v));
                }
                break;
            }
            case ast::EK::Str: emitK(VOP_LOADK, dst, 0, kStr(e->text)); break;
            default: break;
        }
    }

    void cExpr(ast::Expr* e, int dst);
    void cExprName(const std::string& n, int dst);
    bool cExprM(ast::Expr* e, int dst);

    struct CallPlan {
        int fixed = 0;
        bool tailMulti = false;
        bool method = false;
        int keyK = -1;
        bool idxName = false;
    };

    void cCallSetup(ast::Expr* e, int dst, bool parenTrunc, CallPlan& plan) {
        ensureFree(dst + 1);
        int savedTop = cur_->freereg;
        cur_->freereg = dst + 1;
        size_t na = e->args.size();
        plan.fixed = 0;
        plan.tailMulti = false;
        plan.method = e->kind == ast::EK::MCall;
        plan.idxName = false;
        bool deferLoad = !plan.method && e->a && e->a->kind == ast::EK::Index &&
                         e->a->a && e->a->a->kind == ast::EK::Name &&
                         e->a->b && e->a->b->kind == ast::EK::Str;
        if (plan.method) {
            cExpr(e->a, dst + 1);
            plan.keyK = kStr(e->text);
        } else if (deferLoad) {
            plan.idxName = true;
        } else {
            cExpr(e->a, dst);
        }
        for (size_t i = 0; i < na; ++i) {
            int r = dst + 1 + (plan.method ? 1 : 0) + (int)i;
            ensureFree(r);
            if (i + 1 == na) {
                plan.tailMulti = cExprM(e->args[i], r);
                if (!plan.tailMulti) plan.fixed++;
            } else {
                cExpr(e->args[i], r);
                plan.fixed++;
            }
        }
        cur_->freereg = savedTop;
        if (plan.method && plan.tailMulti) {
            emitK(VOP_SELF, dst, dst + 1, plan.keyK);
        } else if (plan.idxName) {
            int tv = dst + 1 + plan.fixed + (plan.tailMulti ? 1 : 0);
            ensureFree(tv);
            cur_->freereg = tv + 1;
            cExpr(e->a->a, tv);
            emitK(VOP_GETT_K, dst, tv, kStr(e->a->b->text));
            cur_->freereg = savedTop;
        }
    }

    void cCallCommon(ast::Expr* e, int dst, int wantC, bool parenTrunc) {
        CallPlan plan;
        cCallSetup(e, dst, parenTrunc, plan);
        VInstr i;
        if (plan.method && !plan.tailMulti) {
            i.op = VOP_SCALL;
            i.a = dst;
            i.b = dst + 1;
            i.k = plan.keyK;
            i.c = wantC;
            i.s = plan.fixed + 2;
        } else if (plan.tailMulti) {
            i.op = VOP_CALLM;
            i.a = dst;
            i.b = plan.fixed + (plan.method ? 1 : 0);
            i.c = wantC;
        } else {
            i.op = VOP_CALL;
            i.a = dst;
            i.b = plan.fixed + 1;
            i.c = wantC;
            if (!plan.method && !plan.tailMulti) {
                if (plan.fixed == 1) { i.op = VOP_CALL1; i.b = wantC; }
                else if (plan.fixed == 2) { i.op = VOP_CALL2; i.b = wantC; }
                else if (plan.fixed == 3) { i.op = VOP_CALL3; i.b = wantC; }
            }
        }
        emit(i);
    }

    void cCompare(ast::Expr* e, int dst) {
        using SO = ast::SO;
        if (e->b && isConstKind(e->b) && e->a && !isConstKind(e->a)) {
            int t1 = reserve();
            cExpr(e->a, t1);
            int kop = kJumpBase(e->op);
            int j = emitJumpK(kop, t1, 0, kIndexOf(e->b), -1);
            simple(VOP_LOADFALSE, dst);
            int jend = emitJump(VOP_JMP, 0, 0, -1);
            at(j).target = here();
            simple(VOP_LOADTRUE, dst);
            at(jend).target = here();
            return;
        }
        if (e->a && isConstKind(e->a) && e->b && !isConstKind(e->b)) {
            int t1 = reserve();
            cExpr(e->b, t1);
            int kop = kJumpLeft(e->op);
            int j = emitJumpK(kop, t1, 0, kIndexOf(e->a), -1);
            simple(VOP_LOADFALSE, dst);
            int jend = emitJump(VOP_JMP, 0, 0, -1);
            at(j).target = here();
            simple(VOP_LOADTRUE, dst);
            at(jend).target = here();
            return;
        }
        int vop;
        switch (e->op) {
            case SO::Lt: vop = VOP_IFLT; break;
            case SO::Le: vop = VOP_IFLE; break;
            case SO::Gt: vop = VOP_IFGT; break;
            case SO::Ge: vop = VOP_IFGE; break;
            case SO::Eq: vop = VOP_IFEQ; break;
            default: vop = VOP_IFNE; break;
        }
        int t1 = reserve();
        cExpr(e->a, t1);
        int t2 = reserve();
        cExpr(e->b, t2);
        int j = emitJump(vop, t1, t2, -1);
        simple(VOP_LOADFALSE, dst);
        int jend = emitJump(VOP_JMP, 0, 0, -1);
        int jtrue = here();
        simple(VOP_LOADTRUE, dst);
        at(j).target = jtrue;
        at(jend).target = here();
    }

    void cAndOr(ast::Expr* e, int dst) {
        bool isAnd = e->op == ast::SO::And;
        if (isConstKind(e->a)) {
            if (isAnd ? !constTruthy(e->a) : constTruthy(e->a)) {
                cConst(e->a, dst);
                return;
            }
            cExpr(e->b, dst);
            return;
        }
        cExpr(e->a, dst);
        int j = emitJump(isAnd ? VOP_JIFF : VOP_JIFT, dst, 0, -1);
        cExpr(e->b, dst);
        at(j).target = here();
    }

    static int invCmp(int op) {
        switch (op) {
            case VOP_IFEQ: return VOP_IFNE;
            case VOP_IFNE: return VOP_IFEQ;
            case VOP_IFLT: return VOP_IFGE;
            case VOP_IFLE: return VOP_IFGT;
            case VOP_IFGT: return VOP_IFLE;
            default: return VOP_IFLT;
        }
    }

    static int invLenCmp(int op) {
        switch (op) {
            case VOP_FLEQ: return VOP_FLNE;
            case VOP_FLNE: return VOP_FLEQ;
            case VOP_FLLT: return VOP_FLGE;
            case VOP_FLLE: return VOP_FLGT;
            case VOP_FLGT: return VOP_FLLE;
            default: return VOP_FLLT;
        }
    }

    static int complementK(int op) {
        switch (op) {
            case VOP_IFEK: return VOP_IFNK;
            case VOP_IFNK: return VOP_IFEK;
            case VOP_IFLTK: return VOP_IFGEK;
            case VOP_IFLEK: return VOP_IFGTK;
            case VOP_IFGTK: return VOP_IFLEK;
            case VOP_IFGEK: return VOP_IFLTK;
            case VOP_IFKLT: return VOP_IFKGE;
            case VOP_IFKLE: return VOP_IFKGT;
            case VOP_IFKGT: return VOP_IFKLE;
            default: return VOP_IFKLT;
        }
    }

    int emitJumpK(int op, int a, int b, int k, int target) {
        VInstr i;
        i.op = op;
        i.a = a;
        i.b = b;
        i.k = k;
        i.target = target;
        i.jump = true;
        return emit(i);
    }

    int cCondJump(ast::Expr* e, bool whenFalse) {
        using SO = ast::SO;
        if (e && e->kind == ast::EK::Un && e->uop == ast::UO::Not)
            return cCondJump(e->a, !whenFalse);
        if (e && e->kind == ast::EK::Bin && e->op >= SO::Eq && e->op <= SO::Ge) {
            int base;
            switch (e->op) {
                case SO::Lt: base = VOP_IFLT; break;
                case SO::Le: base = VOP_IFLE; break;
                case SO::Gt: base = VOP_IFGT; break;
                case SO::Ge: base = VOP_IFGE; break;
                case SO::Eq: base = VOP_IFEQ; break;
                default: base = VOP_IFNE; break;
            }
            if (whenFalse) base = invCmp(base);
            double dv;
            if ((base == VOP_IFEK || base == VOP_IFNK || base == VOP_IFEQ ||
                 base == VOP_IFNE) && isNumExpr(e->b, dv)) {
                int t = reserve();
                cExpr(e->a, t);
                int jk = emitJumpK(base == VOP_IFEQ ? VOP_IFEK : VOP_IFNK, t, 0,
                                   kNum(dv), -1);
                return jk;
            }
            if (e->b && isConstKind(e->b) && e->a && !isConstKind(e->a)) {
                int t = reserve();
                cExpr(e->a, t);
                int kop = kJumpBase(e->op);
                if (whenFalse) kop = complementK(kop);
                return emitJumpK(kop, t, 0, kIndexOf(e->b), -1);
            }
            if (e->a && isConstKind(e->a) && e->b && !isConstKind(e->b)) {
                int t = reserve();
                cExpr(e->b, t);
                int kop = kJumpLeft(e->op);
                if (whenFalse) kop = complementK(kop);
                return emitJumpK(kop, t, 0, kIndexOf(e->a), -1);
            }
            if (e->a && e->a->kind == ast::EK::Un && e->a->uop == ast::UO::Len) {
                int lb;
                switch (e->op) {
                    case SO::Lt: lb = VOP_FLLT; break;
                    case SO::Le: lb = VOP_FLLE; break;
                    case SO::Gt: lb = VOP_FLGT; break;
                    case SO::Ge: lb = VOP_FLGE; break;
                    case SO::Eq: lb = VOP_FLEQ; break;
                    default: lb = VOP_FLNE; break;
                }
                if (whenFalse) lb = invLenCmp(lb);
                int t1 = reserve();
                cExpr(e->a->a, t1);
                int t2 = reserve();
                cExpr(e->b, t2);
                return emitJump(lb, t1, t2, -1);
            }
            int t1 = reserve();
            cExpr(e->a, t1);
            int t2 = reserve();
            cExpr(e->b, t2);
            return emitJump(base, t1, t2, -1);
        }
        int t = reserve();
        cExpr(e, t);
        return emitJump(whenFalse ? VOP_JIFF : VOP_JIFT, t, 0, -1);
    }

    int compileFunction(ast::FuncLit* fn) {
        int pid = newChild((int)fn->params.size(), fn->vararg);
        FG* saved = cur_;
        FG nf;
        nf.p = byId_[pid];
        nf.pid = pid;
        nf.parent = saved;
        cur_ = &nf;
        CBScope fnScope;
        fnScope.baseSlot = 1;
        nf.scopes.push_back(fnScope);
        int slot = 1;
        for (const std::string& pn : fn->params) {
            nf.scopes.back().vars.push_back({pn, slot++});
        }
        nf.freereg = slot;
        compileBlock(fn->body);
        finishFunction();
        cur_ = saved;
        return pid;
    }

    void cTable(ast::Expr* e, int dst) {
        size_t n = e->fields.size();
        bool pureList = n > 0 && n <= 20;
        if (pureList) {
            for (const ast::TableField& f : e->fields)
                if (f.keyKind != ast::TableField::KK::None) {
                    pureList = false;
                    break;
                }
        }

        int stored = 0;
        int batch = 0;
        auto flushBatch = [&]() {
            if (batch <= 0) return;
            if (stored % kFlushFields == 0 && batch <= kFlushFields &&
                stored / kFlushFields + 1 <= 255) {
                simple(VOP_SETLIST, dst, batch + 1, stored / kFlushFields + 1);
            } else {
                for (int i = 1; i <= batch; ++i) {
                    VInstr w;
                    w.op = VOP_SETT_I;
                    w.a = dst + i;
                    w.b = dst;
                    w.s = stored + i;
                    emit(w);
                }
            }
            stored += batch;
            batch = 0;
        };
        auto appendBox = [&](int rbox) {
            if (rbox != dst + 1) simple(VOP_MOVE, dst + 1, rbox);
            int c = stored + 1;
            if (c > 255) c = 0;
            simple(VOP_SETLIST, dst, 0, c);
        };
        if (pureList) {
            for (size_t i = 0; i + 1 < n; ++i) {
                int r = dst + 1 + batch;
                ensureFree(r);
                cExpr(e->fields[i].value, r);
                batch++;
                if (batch == kFlushFields) flushBatch();
            }
            int r = dst + 1 + batch;
            ensureFree(r);
            bool expanded = cExprM(e->fields[n - 1].value, r);
            if (!expanded) {
                if (stored == 0) {
                    simple(VOP_NEWTAB_LIST, dst, (int)n);
                    return;
                }
                batch++;
                flushBatch();
                return;
            }
            simple(VOP_NEWTABLE, dst);
            flushBatch();
            appendBox(r);
            return;
        }
        simple(VOP_NEWTABLE, dst);
        for (size_t i = 0; i < n; ++i) {
            const ast::TableField& f = e->fields[i];
            if (f.keyKind == ast::TableField::KK::None) {
                bool isLast = (i + 1 == n);
                if (isLast) {
                    int r = dst + 1 + batch;
                    ensureFree(r);
                    bool expanded = cExprM(f.value, r);
                    if (expanded) {
                        flushBatch();
                        appendBox(r);
                    } else {
                        batch++;
                        flushBatch();
                    }
                } else {
                    int r = dst + 1 + batch;
                    ensureFree(r);
                    cExpr(f.value, r);
                    batch++;
                    if (batch == kFlushFields) flushBatch();
                }
            } else {
                flushBatch();
                if (f.keyKind == ast::TableField::KK::NameK) {
                    int vr = reserve();
                    cExpr(f.value, vr);
                    emitK(VOP_SETT_K, vr, dst, kStr(f.name));
                } else {
                    double kv;
                    if (isNumExpr(f.keyExpr, kv) && smallInt(kv)) {
                        int vr = reserve();
                        cExpr(f.value, vr);
                        VInstr i2;
                        i2.op = VOP_SETT_I;
                        i2.a = vr;
                        i2.b = dst;
                        i2.s = (std::int64_t)kv;
                        emit(i2);
                    } else {
                        int kr = reserve();
                        cExpr(f.keyExpr, kr);
                        const std::string* vs;
                        double dv;
                        if (isStrExpr(f.value, vs)) {
                            VInstr i2;
                            i2.op = VOP_SETTRK;
                            i2.b = dst;
                            i2.c = kr;
                            i2.k = kStr(*vs);
                            emit(i2);
                        } else if (isNumExpr(f.value, dv)) {
                            VInstr i2;
                            i2.op = VOP_SETTRK;
                            i2.b = dst;
                            i2.c = kr;
                            i2.k = kNum(dv);
                            emit(i2);
                        } else {
                            int vr = reserve();
                            cExpr(f.value, vr);
                            simple(VOP_SETT, vr, dst, kr);
                        }
                    }
                }
            }
        }
        flushBatch();
    }

    void cConcat(ast::Expr* e, int dst) {
        std::vector<ast::Expr*> terms;
        std::vector<ast::Expr*> stack;
        stack.push_back(e);
        while (!stack.empty()) {
            ast::Expr* x = stack.back();
            stack.pop_back();
            if (x->kind == ast::EK::Bin && x->op == ast::SO::Concat && !x->paren) {
                stack.push_back(x->b);
                stack.push_back(x->a);
            } else {
                terms.push_back(x);
            }
        }
        if (terms.size() == 1) {
            cExpr(terms[0], dst);
            return;
        }
        size_t idx = 0;
        int acc = -1;
        {
            bool allStr = true;
            std::string folded;
            for (ast::Expr* x : terms) {
                if (x->kind != ast::EK::Str) {
                    allStr = false;
                    break;
                }
            }
            if (allStr) {
                for (ast::Expr* x : terms) folded += x->text;
                emitK(VOP_LOADK, dst, 0, kStr(folded));
                return;
            }
            ast::Expr* lastT = terms.back();
            const std::string* lcs;
            double ldv;
            bool tailStr = isStrExpr(lastT, lcs);
            bool tailNum = !tailStr && isNumExpr(lastT, ldv);
            if ((tailStr || tailNum) && terms.size() >= 2) {
                size_t head = terms.size() - 1;
                if (head == 1) {
                    int b1 = reserve();
                    cExpr(terms[0], b1);
                    int kk = tailStr ? kStr(*lcs) : kNum(ldv);
                    emitK(VOP_CONCATK, dst, b1, kk);
                } else {
                    int base = reserveN((int)head);
                    for (size_t i = 0; i < head; ++i) cExpr(terms[i], base + (int)i);
                    simple(VOP_CONCAT, dst, base, base + (int)head - 1);
                    int kk = tailStr ? kStr(*lcs) : kNum(ldv);
                    emitK(VOP_CONCATK, dst, dst, kk);
                }
                return;
            }
        }
        if (terms.size() == 2) {
            int base = reserveN(2);
            cExpr(terms[0], base);
            cExpr(terms[1], base + 1);
            simple(VOP_CONCAT2, dst, base, base + 1);
            return;
        }
        if (terms.size() == 3) {
            int base = reserveN(3);
            cExpr(terms[0], base);
            cExpr(terms[1], base + 1);
            cExpr(terms[2], base + 2);
            simple(VOP_CONCAT3, dst, base, 0);
            return;
 }
        while (idx < terms.size()) {
            size_t remain = terms.size() - idx;
            size_t take = std::min(remain, (size_t)kMaxConcat);
            if (acc >= 0 && take > (size_t)kMaxConcat - 1) take = kMaxConcat - 1;
            int cnt = (int)take + (acc >= 0 ? 1 : 0);
            int base = reserveN(cnt);
            int w = base;
            if (acc >= 0) {
                simple(VOP_MOVE, base, acc);
                w = base + 1;
            }
            for (size_t i = 0; i < take; ++i) {
                cExpr(terms[idx + i], w + (int)i);
            }
            int out = (idx + take >= terms.size()) ? dst : reserve();
            simple(VOP_CONCAT, out, base, base + cnt - 1);
            acc = out;
            idx += take;
        }
    }

    bool foldArith(ast::SO op, double da, double db, int dst) {
        double r = 0;
        switch (op) {
            case ast::SO::Add: r = da + db; break;
            case ast::SO::Sub: r = da - db; break;
            case ast::SO::Mul: r = da * db; break;
            case ast::SO::Div: if (db != 0) r = da / db; else return false; break;
            case ast::SO::Mod: if (db != 0) r = std::fmod(da, db); else return false; break;
            case ast::SO::Pow: r = std::pow(da, db); break;
            default: return false;
        }
        VConst c;
        c.t = VConst::NUM;
        c.n = r;
        (void)c;
        if (r == std::floor(r) && std::fabs(r) <= (double)kMaxS24) {
            VInstr i;
            i.op = VOP_LOADINT;
            i.a = dst;
            i.s = (std::int64_t)r;
            emit(i);
        } else {
            emitK(VOP_LOADK, dst, 0, kNum(r));
        }
        return true;
    }

    static int arithOp(ast::SO op) {
        switch (op) {
            case ast::SO::Add: return VOP_ADD;
            case ast::SO::Sub: return VOP_SUB;
            case ast::SO::Mul: return VOP_MUL;
            case ast::SO::Div: return VOP_DIV;
            case ast::SO::Mod: return VOP_MOD;
            case ast::SO::Pow: return VOP_POW;
            default: return -1;
        }
    }

    static int kOp(int arith) {
        switch (arith) {
            case VOP_ADD: return VOP_ADDK;
            case VOP_SUB: return VOP_SUBK;
            case VOP_MUL: return VOP_MULK;
            case VOP_DIV: return VOP_DIVK;
            case VOP_MOD: return VOP_MODK;
            case VOP_POW: return VOP_POWK;
            default: return -1;
        }
    }

    void cExprImpl(ast::Expr* e, int dst) {
        using EK = ast::EK;
        using SO = ast::SO;
        switch (e->kind) {
            case EK::Nil: case EK::True: case EK::False: case EK::Num: case EK::Str:
                cConst(e, dst);
                break;
            case EK::Vararg:
                simple(VOP_VARARG1, dst);
                break;
            case EK::Name:
                cExprName(e->text, dst);
                break;
            case EK::Index: {
                const std::string* cs;
                if (e->a && e->a->kind == ast::EK::Index) {
                    const std::string* cs1;
                    bool aStr = isStrExpr(e->a->b, cs1);
                    bool bConst = e->b && isConstKind(e->b);
                    bool bStr = isStrExpr(e->b, cs);
                    if (aStr && !bConst && e->b) {
                        int obj = reserve();
                        cExpr(e->a->a, obj);
                        int kr = reserve();
                        cExpr(e->b, kr);
                        VInstr i;
                        i.op = VOP_GETTK;
                        i.a = dst;
                        i.b = obj;
                        i.c = kr;
                        i.k = kStr(*cs1);
                        emit(i);
                        break;
                    }
                    if (!aStr && bStr) {
                        int obj = reserve();
                        cExpr(e->a->a, obj);
                        int kr = reserve();
                        cExpr(e->a->b, kr);
                        VInstr i;
                        i.op = VOP_GETTRK;
                        i.a = dst;
                        i.b = obj;
                        i.c = kr;
                        i.k = kStr(e->b->text);
                        emit(i);
                        break;
                    }
                }
                int obj = reserve();
                cExpr(e->a, obj);
                double idv;
                if (isNumExpr(e->b, idv) && smallInt(idv)) {
                    VInstr i;
                    i.op = VOP_GETT_I;
                    i.a = dst;
                    i.b = obj;
                    i.s = (std::int64_t)idv;
                    emit(i);
                    break;
                }
                if (isStrExpr(e->b, cs)) {
                    emitK(VOP_GETT_K, dst, obj, kStr(*cs));
                } else {
                    int kr = reserve();
                    cExpr(e->b, kr);
                    simple(VOP_GETT, dst, obj, kr);
                }
                break;
            }
            case EK::Call:
            case EK::MCall:
                cCallCommon(e, dst, 2, e->paren);
                break;
            case EK::Func:
                compileFunction(e->fn);
                emitK(VOP_CLOSURE, dst, 0, (int)cur_->p->children.size());
                break;
            case EK::Table:
                cTable(e, dst);
                break;
            case EK::Bin: {
                SO op = e->op;
                if (op == SO::And || op == SO::Or) {
                    cAndOr(e, dst);
                    break;
                }
                if (op >= SO::Eq && op <= SO::Ge) {
                    cCompare(e, dst);
                    break;
                }
                if (op == SO::Concat) {
                    cConcat(e, dst);
                    break;
                }
                double da, db;
                if (isNumExpr(e->a, da) && isNumExpr(e->b, db) && foldArith(op, da, db, dst)) {
                    break;
                }
                int aop = arithOp(op);
                if (isNumExpr(e->b, db)) {
                    double dbv = db;
                    if ((op == SO::Add || op == SO::Sub || op == SO::Mul) &&
                        smallInt(dbv)) {
                        int t = reserve();
                        cExpr(e->a, t);
                        VInstr i;
                        i.op = op == SO::Add ? VOP_ADDI
                             : op == SO::Sub ? VOP_SUBI : VOP_MULI;
                        i.a = dst;
                        i.b = t;
                        i.s = (std::int64_t)dbv;
                        emit(i);
                        break;
                    }
                    int t = reserve();
                    cExpr(e->a, t);
                    emitK(kOp(aop), dst, t, kNum(db));
                    break;
                }
                if (isNumExpr(e->a, da)) {
                    double dav = da;
                    if ((op == SO::Add || op == SO::Mul) && smallInt(dav)) {
                        int t = reserve();
                        cExpr(e->b, t);
                        VInstr i;
                        i.op = op == SO::Add ? VOP_ADDI : VOP_MULI;
                        i.a = dst;
                        i.b = t;
                        i.s = (std::int64_t)dav;
                        emit(i);
                        break;
                    }
                    if (op == SO::Sub || op == SO::Div || op == SO::Pow) {
                        int t = reserve();
                        cExpr(e->b, t);
                        int rop = op == SO::Sub ? VOP_RSUBK
                                : op == SO::Div ? VOP_RDIVK : VOP_RPOWK;
                        emitK(rop, dst, t, kNum(da));
                        break;
                    }
                    int t = reserve();
                    cExpr(e->b, t);
                    emitK(kOp(aop), dst, t, kNum(da));
                    break;
                }
                int t1 = reserve();
                cExpr(e->a, t1);
                int t2 = reserve();
                cExpr(e->b, t2);
                simple(aop, dst, t1, t2);
                break;
            }
            case EK::Un: {
                if (e->uop == ast::UO::Not && isConstKind(e->a)) {
                    if (constTruthy(e->a)) simple(VOP_LOADFALSE, dst);
                    else simple(VOP_LOADTRUE, dst);
                    break;
                }
                int t = reserve();
                cExpr(e->a, t);
                int uop = e->uop == ast::UO::Neg ? VOP_UNM
                        : e->uop == ast::UO::Not ? VOP_NOT : VOP_LEN;
                simple(uop, dst, t);
                break;
            }
        }
    }

public:
    void compileStmt(ast::Stmt* st);
};

void Compiler::cExprName(const std::string& n, int dst) {
    int slot = findLocal(cur_, n);
    if (slot >= 0) {
        if (slot != dst) simple(VOP_MOVE, dst, slot);
        return;
    }
    int ui = resolveUpval(cur_, n);
    if (ui >= 0) {
        simple(VOP_GETUPVAL, dst, ui);
        return;
    }
    emitK(VOP_GETGLOBAL, dst, 0, kStr(n));
}

bool Compiler::cExprM(ast::Expr* e, int dst) {
    if (!e) {
        simple(VOP_LOADNIL, dst);
        return false;
    }
    if (e->paren) {
        cExprImpl(e, dst);
        return false;
    }
    if (e->kind == ast::EK::Call || e->kind == ast::EK::MCall) {
        cCallCommon(e, dst, 0, false);
        return true;
    }
    if (e->kind == ast::EK::Vararg) {
        VInstr i;
        i.op = VOP_VARARG;
        i.a = dst;
        i.b = 0;
        emit(i);
        return true;
    }
    cExprImpl(e, dst);
    return false;
}

void Compiler::cExpr(ast::Expr* e, int dst) {
    if (!e) {
        simple(VOP_LOADNIL, dst);
        return;
    }
    cExprImpl(e, dst);
}

void Compiler::compileStmt(ast::Stmt* st) {
    using SK = ast::Stmt::K;
    switch (st->kind) {
        case SK::Empty:
            break;
        case SK::Local: {
            size_t nn = st->names.size();
            size_t ne = st->exprs.size();
            if (ne == 0) {
                int base = reserveN((int)nn);
                CBScope& s = cur_->scopes.back();
                for (size_t i = 0; i < nn; ++i) {
                    s.vars.push_back({st->names[i], base + (int)i});
                    simple(VOP_LOADNIL, base + (int)i);
                }
                break;
            }
            int base = cur_->freereg;
            {
                bool pairConst = ne >= 2 && st->exprs[0] && st->exprs[1] &&
                                 isConstKind(st->exprs[0]) && isConstKind(st->exprs[1]);
                if (pairConst) {
                    int k1 = kIndexOf(st->exprs[0]);
                    int k2 = kIndexOf(st->exprs[1]);
                    VInstr i;
                    i.op = VOP_LOAD2K;
                    i.a = base;
                    i.b = k2;
                    i.k = k1;
                    emit(i);
                    ensureFree(base + 1);
                    for (size_t i2 = 2; i2 + 1 < ne; ++i2) {
                        ensureFree(base + (int)i2);
                        cExpr(st->exprs[i2], base + (int)i2);
                    }
                    ensureFree(base + (int)ne - 1);
                    bool multi2 = cExprM(st->exprs[ne - 1], base + (int)ne - 1);
                    CBScope& s2x = cur_->scopes.back();
                    if (multi2) {
                        simple(VOP_SPILL, base + (int)ne - 1, (int)nn);
                        for (size_t i2 = 0; i2 < nn; ++i2)
                            s2x.vars.push_back({st->names[i2], base + (int)i2});
                        cur_->freereg = base + (int)nn;
                    } else {
                        size_t have = std::min(ne, nn);
                        for (size_t i2 = 0; i2 < have; ++i2)
                            s2x.vars.push_back({st->names[i2], base + (int)i2});
                        for (size_t i2 = have; i2 < nn; ++i2) {
                            s2x.vars.push_back({st->names[i2], base + (int)i2});
                            ensureFree(base + (int)i2);
                            simple(VOP_LOADNIL, base + (int)i2);
                        }
                        cur_->freereg = base + (int)nn;
                    }
                    break;
                }
            }
            for (size_t i = 0; i + 1 < ne; ++i) {
                ensureFree(base + (int)i);
                cExpr(st->exprs[i], base + (int)i);
            }
            ensureFree(base + (int)ne - 1);
            bool multi = cExprM(st->exprs[ne - 1], base + (int)ne - 1);
            CBScope& s = cur_->scopes.back();
            if (multi) {
                simple(VOP_SPILL, base + (int)ne - 1, (int)nn);
                for (size_t i = 0; i < nn; ++i)
                    s.vars.push_back({st->names[i], base + (int)i});
                cur_->freereg = base + (int)nn;
            } else {
                size_t have = std::min(ne, nn);
                for (size_t i = 0; i < have; ++i)
                    s.vars.push_back({st->names[i], base + (int)i});
                for (size_t i = have; i < nn; ++i) {
                    s.vars.push_back({st->names[i], base + (int)i});
                    ensureFree(base + (int)i);
                    simple(VOP_LOADNIL, base + (int)i);
                }
                cur_->freereg = base + (int)nn;
            }
            break;
        }
        case SK::LocalFunc: {
            int slot = reserve();
            cur_->scopes.back().vars.push_back({st->names[0], slot});
            compileFunction(st->fn);
            emitK(VOP_CLOSURE, slot, 0, (int)cur_->p->children.size());
            break;
        }
        case SK::Assign: {
            size_t nt = st->targets.size();
            size_t ne = st->exprs.size();
            int base = reserveN((int)nt);
            for (size_t i = 0; i + 1 < ne; ++i) cExpr(st->exprs[i], base + (int)i);
            if (ne > 0) {
                ensureFree(base + (int)ne - 1);
                bool multi = cExprM(st->exprs[ne - 1], base + (int)ne - 1);
                if (multi) {
                    int fill = (int)nt - (int)ne + 1;
                    simple(VOP_SPILL, base + (int)ne - 1, fill);
                }
            } else {
                for (size_t i = 0; i < nt; ++i) simple(VOP_LOADNIL, base + (int)i);
            }
            for (size_t i = 0; i < nt; ++i) {
                ast::Expr* t = st->targets[i];
                int vreg = base + (int)i;
                if (t->kind == ast::EK::Name) {
                    int slot = findLocal(cur_, t->text);
                    if (slot >= 0) {
                        if (slot != vreg) simple(VOP_MOVE, slot, vreg);
                    } else {
                        int ui = resolveUpval(cur_, t->text);
                        if (ui >= 0) simple(VOP_SETUPVAL, vreg, ui);
                        else emitK(VOP_SETGLOBAL, vreg, 0, kStr(t->text));
                    }
                } else if (t->kind == ast::EK::Index) {
                    const std::string* cs;
                    int obj = reserve();
                    cExpr(t->a, obj);
                    double idv;
                    if (isNumExpr(t->b, idv) && smallInt(idv)) {
                        VInstr i;
                        i.op = VOP_SETT_I;
                        i.a = vreg;
                        i.b = obj;
                        i.s = (std::int64_t)idv;
                        emit(i);
                    } else if (isStrExpr(t->b, cs)) {
                        emitK(VOP_SETT_K, vreg, obj, kStr(*cs));
                    } else {
                        int kr = reserve();
                        cExpr(t->b, kr);
                        simple(VOP_SETT, vreg, obj, kr);
                    }
                }
            }
            break;
        }
        case SK::Call: {
            int t = reserve();
            cCallCommon(st->call, t, 1, st->call->paren);
            break;
        }
        case SK::Do:
            enterScope();
            compileBlock(st->body);
            exitScope();
            break;
        case SK::If: {
            std::vector<int> endPatches;
            for (size_t ci = 0; ci < st->clauses.size(); ++ci) {
                const ast::IfClause& cl = st->clauses[ci];
                int j = cCondJump(cl.cond, true);
                enterScope();
                compileBlock(cl.body);
                exitScope();
                if (ci + 1 < st->clauses.size() || st->elseBody) {
                    endPatches.push_back(emitJump(VOP_JMP, 0, 0, -1));
                }
                at(j).target = here();
            }
            if (st->elseBody) {
                enterScope();
                compileBlock(st->elseBody);
                exitScope();
            }
            int endId = (int)cur_->p->code.size();
            for (int ep : endPatches) at(ep).target = endId;
            break;
        }
        case SK::While: {
            enterScope(true, 1);
            int top = here();
            int jend = cCondJump(st->exprs[0], true);
            compileBlock(st->body);
            emitCloseIf(cur_->scopes.back().baseSlot);
            emitJump(VOP_JMP, 0, 0, top);
            at(jend).target = here();
            for (int cp : cur_->scopes.back().contPatches) at(cp).target = top;
            exitScope();
            break;
        }
        case SK::Repeat: {
            enterScope(true, 2);
            int top = here();
            compileBlock(st->body);
            int jend = cCondJump(st->exprs[0], false);
            emitCloseIf(cur_->scopes.back().baseSlot);
            emitJump(VOP_JMP, 0, 0, top);
            at(jend).target = here();
            for (int cp : cur_->scopes.back().contPatches) at(cp).target = top;
            exitScope();
            break;
        }
        case SK::NumFor: {
            enterScope(true, 3);
            CBScope& sc = cur_->scopes.back();
            int s0 = reserveN(4);
            sc.hiddenSlots = 3;
            sc.vars.push_back({st->names[0], s0 + 3});
            cExpr(st->exprs[0], s0);
            cExpr(st->exprs[1], s0 + 1);
            double stepv;
            bool step1 = st->exprs.size() < 3 ||
                         (isNumExpr(st->exprs[2], stepv) && stepv == 1.0);
            if (step1) {
                int prep = emitJump(VOP_FORPREP1, s0, 0, -1);
                int bodyStart = here();
                compileBlock(st->body);
                emitCloseIf(s0 + 3);
                int floop = emitJump(VOP_FORLOOP1, s0, 0, bodyStart);
                at(prep).target = floop;
                for (int cp : cur_->scopes.back().contPatches) at(cp).target = floop;
                exitScope();
                break;
            }
            cExpr(st->exprs[2], s0 + 2);
            int prep = emitJump(VOP_FORPREP, s0, 0, -1);
            int bodyStart = here();
            compileBlock(st->body);
            emitCloseIf(s0 + 3);
            int floop = emitJump(VOP_FORLOOP, s0, 0, bodyStart);
            at(prep).target = floop;
            for (int cp : cur_->scopes.back().contPatches) at(cp).target = floop;
            exitScope();
            break;
        }
        case SK::GenFor: {
            enterScope(true, 4);
            CBScope& sc = cur_->scopes.back();
            int g0 = reserveN(3 + (int)st->names.size());
            sc.hiddenSlots = 3;
            size_t ne = st->exprs.size();
            if (ne == 0) {
                for (int i = 0; i < 3; ++i) simple(VOP_LOADNIL, g0 + i);
            } else if (ne > 3) {
                cExpr(st->exprs[0], g0);
                cExpr(st->exprs[1], g0 + 1);
                cExpr(st->exprs[2], g0 + 2);
            } else {
                size_t headEnd = std::min(ne, (size_t)3) - 1;
                for (size_t i = 0; i < headEnd; ++i) cExpr(st->exprs[i], g0 + (int)i);
                for (size_t i = headEnd + 1; i < 3; ++i) simple(VOP_LOADNIL, g0 + (int)i);
                int lastPos = g0 + (int)headEnd;
                ensureFree(lastPos);
                bool multi = cExprM(st->exprs[ne - 1], lastPos);
                if (multi) {
                    int fill = 3 - (int)headEnd;
                    simple(VOP_SPILL, lastPos, fill);
                }
            }
            for (size_t i = 0; i < st->names.size(); ++i)
                sc.vars.push_back({st->names[i], g0 + 3 + (int)i});
            int tfor = emitJump(VOP_TFOR, g0, 0, -1);
            at(tfor).c = (int)st->names.size();
            compileBlock(st->body);
            emitCloseIf(g0 + 3);
            emitJump(VOP_JMP, 0, 0, tfor);
            at(tfor).target = here();
            for (int cp : cur_->scopes.back().contPatches) at(cp).target = tfor;
            exitScope();
            break;
        }
        case SK::Break: {
            CBScope* loop = innermostLoop();
            if (loop) {
                emitCloseIf(loop->baseSlot);
                loop->breakPatches.push_back(emitJump(VOP_JMP, 0, 0, -1));
            }
            break;
        }
        case SK::Continue: {
            CBScope* loop = innermostLoop();
            if (loop) {
                emitCloseIf(loop->baseSlot);
                loop->contPatches.push_back(emitJump(VOP_JMP, 0, 0, -1));
            }
            break;
        }
        case SK::Return: {
            size_t ne = st->exprs.size();
            if (ne == 0) {
                simple(VOP_RET0, 0, 0);
                break;
            }
            if (ne == 1) {
                ast::Expr* e = st->exprs[0];
                bool callish = (e->kind == ast::EK::Call || e->kind == ast::EK::MCall) && !e->paren;
                if (callish) {
                    int t = reserve();
                    CallPlan plan;
                    cCallSetup(e, t, false, plan);
                    int extra = e->kind == ast::EK::MCall ? 1 : 0;
                    if (!plan.tailMulti && e->kind == ast::EK::MCall) {
                        VInstr i;
                        i.op = VOP_SCT;
                        i.a = t;
                        i.b = t + 1;
                        i.k = plan.keyK;
                        i.s = plan.fixed + 2;
                        emit(i);
                    } else if (!plan.tailMulti) {
                        VInstr i;
                        i.op = VOP_TAILCALL;
                        i.a = t;
                        i.b = plan.fixed + 1 + extra;
                        emit(i);
                    } else {
                        VInstr i;
                        i.op = VOP_CALLM;
                        i.a = t;
                        i.b = plan.fixed + extra;
                        i.c = 0;
                        emit(i);
                        simple(VOP_RET, t, 0);
                    }
                    break;
                }
                if (e->kind == ast::EK::Vararg && !e->paren) {
                    int t = reserve();
                    VInstr i;
                    i.op = VOP_VARARG;
                    i.a = t;
                    i.b = 0;
                    emit(i);
                    simple(VOP_RET, t, 0);
                    break;
                }
            }
            int base = reserveN((int)ne);
            for (size_t i = 0; i + 1 < ne; ++i) cExpr(st->exprs[i], base + (int)i);
            ast::Expr* last = st->exprs[ne - 1];
            bool lastMulti = cExprM(last, base + (int)ne - 1);
            if (lastMulti && ne > 1) {
                VInstr i;
                i.op = VOP_RETM;
                i.a = base;
                i.b = (int)ne - 1;
                emit(i);
            } else if (lastMulti) {
                simple(VOP_RET, base + (int)ne - 1, 0);
            } else if (ne == 1) {
                simple(VOP_RET1, base, 0);
            } else {
                simple(VOP_RET, base, (int)ne + 1);
            }
            break;
        }
        case SK::Func: {
            compileFunction(st->fn);
            int t = reserve();
            emitK(VOP_CLOSURE, t, 0, (int)cur_->p->children.size());
            const std::vector<std::string>& path = st->path;
            if (path.size() == 1 && st->method.empty()) {
                emitK(VOP_SETGLOBAL, t, 0, kStr(path[0]));
            } else {
                int cur = reserve();
                cExprName(path[0], cur);
                for (size_t i = 1; i + 1 < path.size(); ++i) {
                    int nx = reserve();
                    emitK(VOP_GETT_K, nx, cur, kStr(path[i]));
                    cur = nx;
                }
                const std::string& last = st->method.empty() ? path.back() : st->method;
                emitK(VOP_SETT_K, t, cur, kStr(last));
            }
            break;
        }
    }
}

}

VmIR compileVmIR(ast::Chunk& chunk, std::uint64_t seed, const VmOptions& opt) {
    Compiler c(chunk, seed, opt);
    return c.run();
}

}
}
