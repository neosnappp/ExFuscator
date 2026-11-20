#include "astra/emitter/Emitter.hpp"
#include "astra/lexer/Token.hpp"

#include <cmath>
#include <cctype>

namespace astra {

using namespace ast;

std::pair<int, int> Emitter::binPrio(SO op) {
    switch (op) {
        case SO::Or: return {1, 1};
        case SO::And: return {2, 2};
        case SO::Lt: case SO::Gt: case SO::Le:
        case SO::Ge: case SO::Ne: case SO::Eq: return {3, 3};
        case SO::Concat: return {9, 8};
        case SO::Add: case SO::Sub: return {10, 10};
        case SO::Mul: case SO::Div: case SO::IDiv: case SO::Mod: return {11, 11};
        case SO::Pow: return {14, 13};
        default: return {0, 0};
    }
}

bool Emitter::isSuffixed(const Expr* e) {
    switch (e->kind) {
        case EK::Name: case EK::Index: case EK::Call: case EK::MCall:
            return true;
        default:
            return false;
    }
}

static const int kUnaryEmitterPrio = 12;

bool Emitter::needsParens(const Expr* e, int limit) const {
    if (e->kind == EK::Bin) {
        auto pr = binPrio(e->op);
        return pr.first <= limit;
    }
    if (e->kind == EK::Un) return kUnaryEmitterPrio <= limit;
    return false;
}

std::string Emitter::emit(const Chunk& chunk) {
    out_.clear();
    block(chunk.root);
    return out_;
}

void Emitter::block(const Block* b) {
    for (const Stmt* s : b->stats) {
        stmt(s);
    }
}

void Emitter::funcBody(const FuncLit* f, bool skipSelf) {
    out_ += "(";
    size_t first = skipSelf ? 1 : 0;
    for (size_t i = first; i < f->params.size(); ++i) {
        if (i > first) out_ += ",";
        out_ += f->params[i];
    }
    if (f->vararg) {
        if (f->params.size() > first) out_ += ",";
        out_ += "...";
    }
    out_ += ")";
    block(f->body);
    out_ += "end";
}

void Emitter::stringLiteral(const std::string& bytes) {
    out_ += '"';
    for (unsigned char c : bytes) {
        switch (c) {
            case '"': out_ += "\\\""; break;
            case '\\': out_ += "\\\\"; break;
            case '\a': out_ += "\\a"; break;
            case '\b': out_ += "\\b"; break;
            case '\f': out_ += "\\f"; break;
            case '\n': out_ += "\\n"; break;
            case '\r': out_ += "\\r"; break;
            case '\t': out_ += "\\t"; break;
            case '\v': out_ += "\\v"; break;
            default:
                if (c >= 0x20 && c <= 0x7E) {
                    out_ += (char)c;
                } else {
                    char buf[8];
                    std::snprintf(buf, sizeof(buf), "\\%03u", (unsigned)c);
                    out_ += buf;
                }
        }
    }
    out_ += '"';
}

void Emitter::exprList(const std::vector<Expr*>& v) {
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) out_ += ",";
        expr(v[i], 0);
    }
}

void Emitter::args(const std::vector<Expr*>& v) {
    out_ += "(";
    exprList(v);
    out_ += ")";
}

void Emitter::expr(const Expr* e, int limit) {
    if (e->paren) {
        out_ += '(';
        rawExpr(e);
        out_ += ')';
        return;
    }
    if (needsParens(e, limit)) {
        out_ += '(';
        rawExpr(e);
        out_ += ')';
    } else {
        rawExpr(e);
    }
}

void Emitter::rawExpr(const Expr* e) {
    switch (e->kind) {
        case EK::Nil: out_ += "nil"; break;
        case EK::True: out_ += "true"; break;
        case EK::False: out_ += "false"; break;
        case EK::Vararg: out_ += "..."; break;
        case EK::Num: {
            if (!e->text.empty()) out_ += e->text;
            else {
                char buf[40];
                double v = e->num;
                if (v == (double)(long long)v && std::fabs(v) < 9.0e15)
                    std::snprintf(buf, sizeof(buf), "%lld", (long long)v);
                else
                    std::snprintf(buf, sizeof(buf), "%.17g", v);
                out_ += buf;
            }
            break;
        }
        case EK::Str: stringLiteral(e->text); break;
        case EK::Name: out_ += e->text; break;

        case EK::Func:
            out_ += "function";
            funcBody(e->fn);
            break;

        case EK::Table: {
            out_ += '{';
            for (size_t i = 0; i < e->fields.size(); ++i) {
                if (i) out_ += ",";
                const TableField& f = e->fields[i];
                if (f.keyKind == TableField::KK::NameK) {
                    if (isValidIdentifier(f.name)) {
                        out_ += f.name;
                    } else {
                        stringLiteral(f.name);
                    }
                    out_ += '=';
                    expr(f.value, 0);
                } else if (f.keyKind == TableField::KK::ExprK) {
                    out_ += '[';
                    expr(f.keyExpr, 0);
                    out_ += ']';
                    out_ += '=';
                    expr(f.value, 0);
                } else {
                    expr(f.value, 0);
                }
            }
            out_ += '}';
            break;
        }

        case EK::Bin: {
            auto pr = binPrio(e->op);

            const char* sp = e->op == SO::Sub ? " " : "";

            bool alpha = e->op == SO::And || e->op == SO::Or;
            expr(e->a, pr.first);

            bool padL = alpha || (e->op == SO::Concat && !out_.empty() &&
                                  std::isdigit((unsigned char)out_.back()));
            if (padL) out_ += ' ';
            out_ += soSpell(e->op);
            out_ += alpha ? " " : sp;
            expr(e->b, pr.second);
            break;
        }

        case EK::Un: {
            const char* u = e->uop == UO::Neg ? "-" : (e->uop == UO::Len ? "#" : "not ");
            out_ += u;
            expr(e->a, kUnaryEmitterPrio);
            break;
        }

        case EK::Index: {
            if (!isSuffixed(e->a)) {
                out_ += '(';
                rawExpr(e->a);
                out_ += ')';
            } else {
                rawExpr(e->a);
            }
            if (e->b->kind == EK::Str && isValidIdentifier(e->b->text)) {
                out_ += '.';
                out_ += e->b->text;
            } else {
                out_ += '[';
                expr(e->b, 0);
                out_ += ']';
            }
            break;
        }

        case EK::Call: {
            if (!isSuffixed(e->a)) {
                out_ += '(';
                rawExpr(e->a);
                out_ += ')';
            } else {
                rawExpr(e->a);
            }
            args(e->args);
            break;
        }

        case EK::MCall: {
            if (!isSuffixed(e->a)) {
                out_ += '(';
                rawExpr(e->a);
                out_ += ')';
            } else {
                rawExpr(e->a);
            }
            out_ += ':';
            out_ += e->text;
            args(e->args);
            break;
        }
    }
}

void Emitter::stmt(const Stmt* s) {
    switch (s->kind) {
        case Stmt::K::Empty: out_ += ";"; break;

        case Stmt::K::Local: {
            out_ += "local";
            for (size_t i = 0; i < s->names.size(); ++i) {
                out_ += i ? "," : " ";
                out_ += s->names[i];
            }
            if (!s->exprs.empty()) {
                out_ += '=';
                exprList(s->exprs);
            }
            out_ += ';';
            break;
        }

        case Stmt::K::LocalFunc: {
            out_ += "local function " + s->names[0];
            funcBody(s->fn);
            out_ += ';';
            break;
        }

        case Stmt::K::Assign: {
            for (size_t i = 0; i < s->targets.size(); ++i) {
                if (i) out_ += ",";
                expr(s->targets[i], 0);
            }
            out_ += '=';
            exprList(s->exprs);
            out_ += ';';
            break;
        }

        case Stmt::K::Call:
            expr(s->call, 0);
            out_ += ';';
            break;

        case Stmt::K::Do:
            out_ += " do ";
            block(s->body);
            out_ += "end;";
            break;

        case Stmt::K::While:
            out_ += "while ";
            expr(s->exprs[0], 0);
            out_ += " do ";
            block(s->body);
            out_ += "end;";
            break;

        case Stmt::K::Repeat:
            out_ += "repeat ";
            block(s->body);
            out_ += "until ";
            expr(s->exprs[0], 0);
            out_ += ';';
            break;

        case Stmt::K::If: {
            for (size_t i = 0; i < s->clauses.size(); ++i) {
                const IfClause& c = s->clauses[i];
                out_ += i == 0 ? "if " : "elseif ";
                expr(c.cond, 0);
                out_ += " then ";
                block(c.body);
            }
            if (s->elseBody) {
                out_ += "else ";
                block(s->elseBody);
            }
            out_ += "end;";
            break;
        }

        case Stmt::K::NumFor: {
            out_ += "for " + s->names[0] + '=';
            expr(s->exprs[0], 0);
            out_ += ',';
            expr(s->exprs[1], 0);
            if (s->exprs.size() > 2) {
                out_ += ',';
                expr(s->exprs[2], 0);
            }
            out_ += " do ";
            block(s->body);
            out_ += "end;";
            break;
        }

        case Stmt::K::GenFor: {
            out_ += "for ";
            for (size_t i = 0; i < s->names.size(); ++i) {
                out_ += i ? "," : "";
                out_ += s->names[i];
            }
            out_ += " in ";
            exprList(s->exprs);
            out_ += " do ";
            block(s->body);
            out_ += "end;";
            break;
        }

        case Stmt::K::Func: {
            out_ += "function ";
            for (const std::string& p : s->path) {
                out_ += p;
                out_ += '.';
            }
            out_.resize(out_.size() - 1);
            if (!s->method.empty()) {
                out_ += ':';
                out_ += s->method;
            }
            funcBody(s->fn, !s->method.empty());
            out_ += ';';
            break;
        }

        case Stmt::K::Return: {
            out_ += "return";
            if (!s->exprs.empty()) {
                out_ += ' ';
                exprList(s->exprs);
            }
            out_ += ';';
            break;
        }

        case Stmt::K::Break: out_ += "break;"; break;
        case Stmt::K::Continue: out_ += "continue;"; break;
    }
}

}
