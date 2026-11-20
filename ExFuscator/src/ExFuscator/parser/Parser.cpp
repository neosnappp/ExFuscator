#include "astra/parser/Parser.hpp"
#include "astra/lexer/Lexer.hpp"
#include "astra/Diagnostic.hpp"

namespace astra {

using namespace ast;

Parser::Parser(std::vector<Token> toks) : toks_(std::move(toks)) {}

Expr* Parser::mkExpr(EK k, int line) {
    auto e = std::make_unique<Expr>(k);
    e->line = line;
    exprArena_.push_back(std::move(e));
    return exprArena_.back().get();
}
Stmt* Parser::mkStmt(Stmt::K k, int line) {
    auto s = std::make_unique<Stmt>(k);
    s->line = line;
    stmtArena_.push_back(std::move(s));
    return stmtArena_.back().get();
}
Block* Parser::mkBlock() {
    blockArena_.push_back(std::make_unique<Block>());
    return blockArena_.back().get();
}
FuncLit* Parser::mkFunc(int line) {
    auto f = std::make_unique<FuncLit>();
    f->line = line;
    funcArena_.push_back(std::move(f));
    return funcArena_.back().get();
}

const Token& Parser::peek(size_t off) const {
    size_t i = p_ + off;
    if (i >= toks_.size()) i = toks_.size() - 1;
    return toks_[i];
}
const Token& Parser::advance() {
    const Token& t = toks_[p_];
    if (p_ + 1 < toks_.size()) ++p_;
    return t;
}
bool Parser::check(TokType t) const { return peek().type == t; }
bool Parser::checkKw(const char* kw) const { return peek().isKw(kw); }
bool Parser::checkOp(const char* op) const { return peek().isOp(op); }
bool Parser::accept(TokType t) {
    if (check(t)) { advance(); return true; }
    return false;
}
bool Parser::acceptKw(const char* kw) {
    if (checkKw(kw)) { advance(); return true; }
    return false;
}
bool Parser::acceptOp(const char* op) {
    if (checkOp(op)) { advance(); return true; }
    return false;
}
const Token& Parser::expect(TokType t, const char* what) {
    if (!check(t))
        fail(std::string(what) + " expected");
    return advance();
}
std::string Parser::expectName(const char* what) {
    const Token& t = expect(TokType::Name, what);
    return t.text;
}
void Parser::expectOp(const char* op) {
    if (!checkOp(op))
        fail(std::string("'") + op + "' expected near '" + peek().text + "'");
    advance();
}
void Parser::expectKw(const char* kw) {
    if (!checkKw(kw))
        fail(std::string("'") + kw + "' expected near '" + peek().text + "'");
    advance();
}
void Parser::fail(const std::string& msg) {
    const Token& t = peek();
    throw AstraError(msg + " near '" + (t.type == TokType::Eof ? "<eof>" : t.text) + "'", t.line, t.col);
}

bool Parser::isCompoundOp(const Token& t, SO& out) {
    if (t.type != TokType::Op) return false;
    if (t.text == "+=") { out = SO::Add; return true; }
    if (t.text == "-=") { out = SO::Sub; return true; }
    if (t.text == "*=") { out = SO::Mul; return true; }
    if (t.text == "/=") { out = SO::Div; return true; }
    if (t.text == "%=") { out = SO::Mod; return true; }
    if (t.text == "^=") { out = SO::Pow; return true; }
    if (t.text == "..=") { out = SO::Concat; return true; }
    if (t.text == "//=") { out = SO::IDiv; return true; }
    return false;
}

Chunk Parser::parse() {
    Chunk ch;

    enterFn();
    ch.root = parseBlock();
    exitFn();
    if (!check(TokType::Eof))
        fail("unexpected token (missing 'end'?)");
    return ch;
}

void Parser::addLocals(int n) {
    if (fnLocals_.empty()) return;
    fnLocals_.back() += n;
    if (fnLocals_.back() > kMaxLocals)
        fail("too many local variables (limit is 200) in a function");
}

Block* Parser::parseBlock() {

    NestGuard ng(this);
    Block* b = mkBlock();
    auto atBlockEnd = [&]() {
        return check(TokType::Eof) || checkKw("end") || checkKw("else") ||
               checkKw("elseif") || checkKw("until");
    };

    int savedLocals = fnLocals_.empty() ? 0 : fnLocals_.back();
    while (!atBlockEnd()) {
        if (acceptOp(";")) continue;
        if (acceptKw("return")) {
            const Token& rt = peek();
            bool hasExprs = !(rt.type == TokType::Eof || checkKw("end") || checkKw("else") ||
                              checkKw("elseif") || checkKw("until") || checkOp(";"));
            Stmt* st = mkStmt(Stmt::K::Return, rt.line);
            if (hasExprs) st->exprs = parseExprList();
            acceptOp(";");
            b->stats.push_back(st);
            break;
        }
        b->stats.push_back(parseStatement());
        acceptOp(";");
    }
    if (!fnLocals_.empty()) fnLocals_.back() = savedLocals;
    return b;
}

Stmt* Parser::parseStatement() {

    NestGuard ng(this);
    const Token& t = peek();
    int line = t.line;

    if (checkOp("::")) fail("labels/goto are not supported in v0.1");
    if (checkKw("goto")) fail("goto is not supported in v0.1");

    switch (t.type) {
        case TokType::Name: {

            Expr* first = parseSuffixed();
            if (checkOp("=") || checkOp(",")) {
                std::vector<Expr*> targets;
                targets.push_back(first);
                while (acceptOp(",")) targets.push_back(parseSuffixed());
                expectOp("=");
                Stmt* st = mkStmt(Stmt::K::Assign, line);
                st->targets = std::move(targets);
                st->exprs = parseExprList();
                for (Expr* tg : st->targets)
                    if (tg->kind != EK::Name && tg->kind != EK::Index)
                        fail("cannot assign to this expression");
                return st;
            }
            {
                SO cop;
                if (isCompoundOp(peek(), cop)) {

                    advance();
                    if (first->kind != EK::Name && first->kind != EK::Index)
                        fail("cannot assign to this expression");
                    Expr* rhs = parseExpr();
                    Expr* bin = mkExpr(EK::Bin, line);
                    bin->op = cop;
                    bin->a = cloneForCompound(first, first->paren);
                    bin->b = rhs;
                    Stmt* st = mkStmt(Stmt::K::Assign, line);
                    st->targets.push_back(first);
                    st->exprs.push_back(bin);
                    return st;
                }
            }
            if (first->kind != EK::Call && first->kind != EK::MCall)
                fail("syntax error (expected '=' or call)");
            Stmt* st = mkStmt(Stmt::K::Call, line);
            st->call = first;
            return st;
        }
        case TokType::Keyword: {
            if (t.text == "break") { advance(); return mkStmt(Stmt::K::Break, line); }
            if (t.text == "continue") { advance(); return mkStmt(Stmt::K::Continue, line); }
            if (t.text == "do") {
                advance();
                Stmt* st = mkStmt(Stmt::K::Do, line);
                st->body = parseBlock();
                expectKw("end");
                return st;
            }
            if (t.text == "while") {
                advance();
                Stmt* st = mkStmt(Stmt::K::While, line);
                st->exprs.push_back(parseExpr());
                expectKw("do");
                st->body = parseBlock();
                expectKw("end");
                return st;
            }
            if (t.text == "repeat") {
                advance();
                Stmt* st = mkStmt(Stmt::K::Repeat, line);
                st->body = parseBlock();
                expectKw("until");
                st->exprs.push_back(parseExpr());
                return st;
            }
            if (t.text == "if") return parseIf();
            if (t.text == "for") {
                advance();
                std::string name = expectName("<name>");
                if (checkOp("=")) return parseNumericFor(name);
                return parseGenericFor(name);
            }
            if (t.text == "function") return parseFuncStatement();
            if (t.text == "local") return parseLocal();
            fail("unexpected '" + t.text + "'");
        }
        default:
            fail("unexpected symbol");
    }
    return nullptr;
}

Expr* Parser::cloneForCompound(Expr* e, bool paren) {
    Expr* n = mkExpr(e->kind, e->line);
    n->num = e->num;
    n->text = e->text;
    n->op = e->op;
    n->uop = e->uop;
    n->paren = paren;
    if (e->a) n->a = cloneForCompound(e->a, e->a->paren);
    if (e->b) n->b = cloneForCompound(e->b, e->b->paren);
    for (Expr* arg : e->args) n->args.push_back(cloneForCompound(arg, arg->paren));
    for (const TableField& f : e->fields) {
        TableField nf = f;
        if (f.keyExpr) nf.keyExpr = cloneForCompound(f.keyExpr);
        if (f.value) nf.value = cloneForCompound(f.value);
        n->fields.push_back(nf);
    }
    if (e->fn) {
        FuncLit* f = mkFunc(e->line);
        f->params = e->fn->params;
        f->vararg = e->fn->vararg;

        Block* nb = mkBlock();
        std::function<Block*(Block*)> cb = [&](Block* src) {
            Block* out = mkBlock();
            for (Stmt* s : src->stats) {
                Stmt* ns = mkStmt(s->kind, s->line);
                ns->names = s->names;
                ns->path = s->path;
                ns->method = s->method;
                for (Expr* x : s->exprs) ns->exprs.push_back(cloneForCompound(x, x->paren));
                for (Expr* x : s->targets) ns->targets.push_back(cloneForCompound(x, x->paren));
                if (s->call) ns->call = cloneForCompound(s->call, s->call->paren);
                if (s->body) ns->body = cb(s->body);
                if (s->elseBody) ns->elseBody = cb(s->elseBody);
                for (const IfClause& c : s->clauses) {
                    IfClause nc;
                    nc.cond = cloneForCompound(c.cond);
                    nc.body = cb(c.body);
                    ns->clauses.push_back(nc);
                }
                if (s->fn) {
                    FuncLit* nf2 = mkFunc(s->line);
                    nf2->params = s->fn->params;
                    nf2->vararg = s->fn->vararg;
                    nf2->body = cb(s->fn->body);
                    ns->fn = nf2;
                }
                out->stats.push_back(ns);
            }
            return out;
        };
        nb = cb(e->fn->body);
        f->body = nb;
        n->fn = f;
    }
    return n;
}

Stmt* Parser::parseIf() {
    int line = peek().line;
    advance();
    Stmt* st = mkStmt(Stmt::K::If, line);
    IfClause c;
    c.cond = parseExpr();
    expectKw("then");
    c.body = parseBlock();
    st->clauses.push_back(c);
    for (;;) {
        if (acceptKw("elseif")) {
            IfClause ec;
            ec.cond = parseExpr();
            expectKw("then");
            ec.body = parseBlock();
            st->clauses.push_back(ec);
        } else if (acceptKw("else")) {
            st->elseBody = parseBlock();
            expectKw("end");
            break;
        } else {
            expectKw("end");
            break;
        }
    }
    return st;
}

Stmt* Parser::parseNumericFor(const std::string& name) {
    int line = peek().line;
    expectOp("=");
    Stmt* st = mkStmt(Stmt::K::NumFor, line);
    st->names.push_back(name);
    st->exprs.push_back(parseExpr());
    expectOp(",");
    st->exprs.push_back(parseExpr());
    if (acceptOp(",")) st->exprs.push_back(parseExpr());
    expectKw("do");

    addLocals((int)st->names.size());
    st->body = parseBlock();
    expectKw("end");
    return st;
}

Stmt* Parser::parseGenericFor(const std::string& first) {
    int line = peek().line;
    Stmt* st = mkStmt(Stmt::K::GenFor, line);
    st->names.push_back(first);
    while (acceptOp(",")) st->names.push_back(expectName("<name>"));
    expectKw("in");
    st->exprs = parseExprList();
    expectKw("do");

    addLocals((int)st->names.size());
    st->body = parseBlock();
    expectKw("end");
    return st;
}

Stmt* Parser::parseFuncStatement() {
    int line = peek().line;
    advance();
    Stmt* st = mkStmt(Stmt::K::Func, line);
    st->path.push_back(expectName("<name>"));
    while (checkOp(".") && st->method.empty())
        { advance(); st->path.push_back(expectName("<name>")); }
    if (checkOp(":")) {
        advance();
        st->method = expectName("<name>");
    }
    st->fn = parseFuncBody(line);

    if (!st->method.empty())
        st->fn->params.insert(st->fn->params.begin(), "self");
    return st;
}

void Parser::parseNameAttributes() {

    if (checkOp("<")) {
        advance();
        std::string attr = expectName("attribute name");
        if (attr == "close")
            fail("<close> variables are not supported in v0.1");
        expectOp(">");
    }
}

void Parser::skipTypeAnnotation() {
    while (true) {
        if (checkOp("(")) {
            advance();
            int d = 1;
            while (d > 0 && !check(TokType::Eof)) {
                if (checkOp("(")) ++d;
                else if (checkOp(")")) --d;
                advance();
            }
        } else if (checkOp("{")) {
            advance();
            int d = 1;
            while (d > 0 && !check(TokType::Eof)) {
                if (checkOp("{")) ++d;
                else if (checkOp("}")) --d;
                advance();
            }
        } else if (checkKw("typeof")) {
            advance();
            expectOp("(");
            int d = 1;
            while (d > 0 && !check(TokType::Eof)) {
                if (checkOp("(")) ++d;
                else if (checkOp(")")) --d;
                advance();
            }
        } else {
            (void)expectName("type name");
            while (acceptOp(".")) (void)expectName("type name");
        }
        acceptOp("?");
        if (!acceptOp("|")) break;
    }
}

Stmt* Parser::parseLocal() {
    int line = peek().line;
    advance();
    if (acceptKw("function")) {
        Stmt* st = mkStmt(Stmt::K::LocalFunc, line);
        st->names.push_back(expectName("<name>"));

        addLocals((int)st->names.size());
        st->fn = parseFuncBody(line);
        return st;
    }
    Stmt* st = mkStmt(Stmt::K::Local, line);
    st->names.push_back(expectName("<name>"));
    parseNameAttributes();
    if (acceptOp(":")) skipTypeAnnotation();
    while (acceptOp(",")) {
        st->names.push_back(expectName("<name>"));
        parseNameAttributes();
        if (acceptOp(":")) skipTypeAnnotation();
    }

    addLocals((int)st->names.size());
    if (acceptOp("=")) st->exprs = parseExprList();
    return st;
}

FuncLit* Parser::parseFuncBody(int line) {

    NestGuard ng(this);
    FuncLit* f = mkFunc(line);
    enterFn();
    expectOp("(");
    if (!checkOp(")")) {
        if (checkOp("...")) {
            advance();
            f->vararg = true;
        } else {
            f->params.push_back(expectName("<name>"));
            while (acceptOp(",")) {
                if (checkOp("...")) { advance(); f->vararg = true; break; }
                f->params.push_back(expectName("<name>"));
            }
        }
    }
    addLocals((int)f->params.size());
    expectOp(")");
    f->body = parseBlock();
    expectKw("end");
    exitFn();
    return f;
}

std::vector<std::string> Parser::parseNameList(const char* what) {
    std::vector<std::string> out;
    out.push_back(expectName(what));
    while (acceptOp(",")) out.push_back(expectName(what));
    return out;
}

struct BinPrio { int left, right; };
static bool getBinOp(const Token& t, SO& op, BinPrio& pr) {
    if (t.type != TokType::Op && t.type != TokType::Keyword) return false;
    struct Row { const char* s; SO op; int l, r; };
    static const Row rows[] = {
        {"or",  SO::Or,  1, 1},
        {"and", SO::And, 2, 2},
        {"<",   SO::Lt,  3, 3}, {">", SO::Gt, 3, 3}, {"<=", SO::Le, 3, 3},
        {">=",  SO::Ge,  3, 3}, {"~=", SO::Ne, 3, 3}, {"==", SO::Eq, 3, 3},
        {"..",  SO::Concat, 9, 8},
        {"+",   SO::Add, 10, 10}, {"-", SO::Sub, 10, 10},
        {"*",   SO::Mul, 11, 11}, {"/", SO::Div, 11, 11}, {"%", SO::Mod, 11, 11},
        {"//",  SO::IDiv, 11, 11},
        {"^",   SO::Pow, 14, 13},
        {nullptr, SO::None, 0, 0},
    };
    for (const Row* r = rows; r->s; ++r)
        if (t.text == r->s) { op = r->op; pr = {r->l, r->r}; return true; }
    return false;
}
static const int kUnaryPrio = 12;

Expr* Parser::parseExpr(int limit) {

    NestGuard ng(this);
    Expr* lhs;

    if (checkOp("-") || checkKw("not") || checkOp("#")) {
        int line = peek().line;
        Token op = advance();
        Expr* operand = parseExpr(kUnaryPrio);
        lhs = mkExpr(EK::Un, line);
        lhs->uop = op.isOp("-") ? UO::Neg : (op.isOp("#") ? UO::Len : UO::Not);
        lhs->a = operand;
    } else {
        lhs = parseSimpleExpr();
    }

    for (;;) {
        SO op;
        BinPrio pr{0, 0};
        if (!getBinOp(peek(), op, pr)) break;
        if (pr.left <= limit) break;
        const Token& opTok = advance();
        Expr* rhs = parseExpr(pr.right);
        Expr* bin = mkExpr(EK::Bin, opTok.line);
        bin->op = op;
        bin->a = lhs;
        bin->b = rhs;
        lhs = bin;
    }
    return lhs;
}

Expr* Parser::parseSimpleExpr() {
    const Token& t = peek();
    int line = t.line;
    switch (t.type) {
        case TokType::Number: {
            advance();
            Expr* e = mkExpr(EK::Num, line);
            e->num = t.num;
            e->text = t.text;
            return e;
        }
        case TokType::String: {
            advance();
            Expr* e = mkExpr(EK::Str, line);
            e->text = t.bytes;
            return e;
        }
        case TokType::Interp: {
            advance();
            return buildInterpString(t);
        }
        case TokType::Keyword: {
            if (t.text == "if") { advance(); return parseIfExpression(line); }
            if (t.text == "nil") { advance(); return mkExpr(EK::Nil, line); }
            if (t.text == "true") { advance(); return mkExpr(EK::True, line); }
            if (t.text == "false") { advance(); return mkExpr(EK::False, line); }
            if (t.text == "function") {
                advance();
                Expr* e = mkExpr(EK::Func, line);
                e->fn = parseFuncBody(line);
                return e;
            }
            break;
        }
        case TokType::Op: {
            if (t.text == "...") { advance(); return mkExpr(EK::Vararg, line); }
            if (t.text == "{") return parseTableConstructor();
            break;
        }
        default: break;
    }
    return parseSuffixed();
}

Expr* Parser::parseSuffixed() {
    Expr* e = parsePrimary();
    for (;;) {
        const Token& t = peek();
        if (t.isOp(".")) {
            advance();
            std::string name = expectName("<name>");
            Expr* idx = mkExpr(EK::Index, t.line);
            idx->a = e;
            Expr* key = mkExpr(EK::Str, t.line);
            key->text = name;
            idx->b = key;
            e = idx;
        } else if (t.isOp("[")) {
            advance();
            Expr* key = parseExpr();
            expectOp("]");
            Expr* idx = mkExpr(EK::Index, t.line);
            idx->a = e;
            idx->b = key;
            e = idx;
        } else if (t.isOp(":")) {
            advance();
            std::string name = expectName("<name>");
            std::vector<Expr*> args = parseCallArgs(nullptr);
            Expr* call = mkExpr(EK::MCall, t.line);
            call->a = e;
            call->text = name;
            call->args = std::move(args);
            e = call;
        } else if (t.isOp("(") || t.isOp("{") || t.type == TokType::String || t.type == TokType::Interp) {
            std::vector<Expr*> args = parseCallArgs(nullptr);
            Expr* call = mkExpr(EK::Call, t.line);
            call->a = e;
            call->args = std::move(args);
            e = call;
        } else {
            break;
        }
    }
    return e;
}

Expr* Parser::parsePrimary() {
    const Token& t = peek();
    int line = t.line;
    if (t.type == TokType::Name) {
        advance();
        Expr* e = mkExpr(EK::Name, line);
        e->text = t.text;
        return e;
    }
    if (t.isOp("(")) {
        advance();
        Expr* inner = parseExpr();
        expectOp(")");
        inner->paren = true;
        return inner;
    }
    if (t.isOp("function")) {
        advance();
        Expr* e = mkExpr(EK::Func, line);
        e->fn = parseFuncBody(line);
        return e;
    }
    fail("unexpected symbol");
    return nullptr;
}

std::vector<Expr*> Parser::parseCallArgs(Expr* ) {
    std::vector<Expr*> args;
    const Token& t = peek();
    if (t.isOp("(")) {
        advance();
        if (!checkOp(")")) args = parseExprList();
        expectOp(")");
    } else if (t.isOp("{")) {
        args.push_back(parseTableConstructor());
    } else if (t.type == TokType::String) {
        advance();
        Expr* e = mkExpr(EK::Str, t.line);
        e->text = t.bytes;
        args.push_back(e);
    } else if (t.type == TokType::Interp) {
        advance();
        args.push_back(buildInterpString(t));
    } else {
        fail("function arguments expected");
    }
    return args;
}

Expr* Parser::parseTableConstructor() {

    NestGuard ng(this);
    int line = peek().line;
    expectOp("{");
    Expr* e = mkExpr(EK::Table, line);
    for (;;) {
        if (checkOp("}")) break;
        TableField f;
        if (checkOp("[")) {
            advance();
            f.keyKind = TableField::KK::ExprK;
            f.keyExpr = parseExpr();
            expectOp("]");
            expectOp("=");
            f.value = parseExpr();
        } else if (peek().type == TokType::Name && peek(1).isOp("=")) {
            f.keyKind = TableField::KK::NameK;
            f.name = advance().text;
            advance();
            f.value = parseExpr();
        } else {
            f.keyKind = TableField::KK::None;
            f.value = parseExpr();
        }
        e->fields.push_back(f);
        if (!acceptOp(",") && !acceptOp(";")) break;
    }
    expectOp("}");
    return e;
}

std::vector<Expr*> Parser::parseExprList() {
    std::vector<Expr*> out;
    out.push_back(parseExpr());
    while (acceptOp(",")) out.push_back(parseExpr());
    return out;
}

Expr* Parser::parseIfExpression(int line) {
    if (std::getenv("EXF_TRACE")) {
        const Token& tk = peek();
        std::fprintf(stderr, "IFEXPR enter at %d:%d tok=%s\n", tk.line, tk.col, tk.text.c_str());
        for (int d = 0; d < 12; ++d) {
            const Token& w = peek(d);
            std::fprintf(stderr, "  +%d [%d] %s\n", d, (int)w.type, w.text.c_str());
        }
    }
    FuncLit* fl = mkFunc(line);
    Block* body = mkBlock();
    Stmt* ifs = mkStmt(Stmt::K::If, line);
    for (;;) {
        IfClause cl;
        cl.cond = parseExpr();
        expectKw("then");
        Expr* val = parseExpr();
        Stmt* ret = mkStmt(Stmt::K::Return, line);
        ret->exprs.push_back(val);
        Block* br = mkBlock();
        br->stats.push_back(ret);
        cl.body = br;
        ifs->clauses.push_back(cl);
        if (acceptKw("elseif")) continue;
        break;
    }
    if (acceptKw("else")) {
        Expr* val = parseExpr();
        Stmt* ret = mkStmt(Stmt::K::Return, line);
        ret->exprs.push_back(val);
        Block* br = mkBlock();
        br->stats.push_back(ret);
        ifs->elseBody = br;
    }
    acceptKw("end");
    body->stats.push_back(ifs);
    fl->body = body;
    Expr* fn = mkExpr(EK::Func, line);
    fn->fn = fl;
    Expr* call = mkExpr(EK::Call, line);
    call->a = fn;
    return call;
}

Expr* Parser::buildInterpString(const Token& t) {
    const auto& segs = t.segs;
    if (segs.empty()) {
        Expr* e = mkExpr(EK::Str, t.line);
        e->text = "";
        return e;
    }
    if (segs.size() == 1 && !segs[0].first) {
        Expr* e = mkExpr(EK::Str, t.line);
        e->text = segs[0].second;
        return e;
    }
    Expr* left = nullptr;
    for (const auto& sg : segs) {
        Expr* node = nullptr;
        if (!sg.first) {
            node = mkExpr(EK::Str, t.line);
            node->text = sg.second;
        } else {
            Expr* inner = parseInterpExprText(sg.second, t.line);
            Expr* call = mkExpr(EK::Call, t.line);
            Expr* callee = mkExpr(EK::Name, t.line);
            callee->text = "tostring";
            call->a = callee;
            call->args.push_back(inner);
            node = call;
        }
        if (!left) { left = node; continue; }
        Expr* bin = mkExpr(EK::Bin, t.line);
        bin->op = SO::Concat;
        bin->a = left;
        bin->b = node;
        left = bin;
    }
    return left;
}

Expr* Parser::parseInterpExprText(const std::string& src, int line) {
    Lexer lx(src, "<interp>");
    std::vector<Token> sub = lx.tokenize();
    Parser subParser(std::move(sub));
    Expr* e = subParser.parseExpr();
    if (!subParser.check(TokType::Eof)) subParser.fail("unexpected symbol in interpolation expression");
    for (auto& p : subParser.exprArena_) exprArena_.push_back(std::move(p));
    subParser.exprArena_.clear();
    return e;
}
}
