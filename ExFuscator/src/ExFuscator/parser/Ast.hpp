#pragma once

#include "astra/Common.hpp"

namespace astra {
namespace ast {

enum class EK {
    Nil, True, False,
    Num,
    Str,
    Vararg,
    Func,
    Table,
    Bin,
    Un,
    Call,
    MCall,
    Index,
    Name,
};

enum class SO {
    Add, Sub, Mul, Div, IDiv, Mod, Pow, Concat,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
    None
};

enum class UO { Not, Neg, Len };

struct Expr;
struct Block;
struct FuncLit;

struct TableField {

    enum class KK { None, ExprK, NameK } keyKind = KK::None;
    std::string name;
    Expr* keyExpr = nullptr;
    Expr* value = nullptr;
};

struct Expr {
    EK kind;
    int line = 0;

    double num = 0.0;
    std::string text;
    SO op = SO::None;
    UO uop = UO::Not;
    Expr* a = nullptr;
    Expr* b = nullptr;
    std::vector<Expr*> args;
    std::vector<TableField> fields;
    FuncLit* fn = nullptr;

    bool paren = false;

    void* binding = nullptr;

    explicit Expr(EK k) : kind(k) {}
};

struct FuncLit {
    std::vector<std::string> params;
    bool vararg = false;
    Block* body = nullptr;
    int line = 0;
};

struct IfClause {
    Expr* cond = nullptr;
    Block* body = nullptr;
};

struct Stmt {
    enum class K {
        Empty,
        Local,
        LocalFunc,
        Assign,
        Call,
        Do,
        While,
        Repeat,
        If,
        NumFor,
        GenFor,
        Func,
        Return,
        Break,
        Continue,
    };
    K kind;
    int line = 0;

    std::vector<std::string> names;
    std::vector<Expr*> exprs;
    std::vector<Expr*> targets;
    Expr* call = nullptr;
    Block* body = nullptr;
    Block* elseBody = nullptr;
    std::vector<IfClause> clauses;
    FuncLit* fn = nullptr;
    std::vector<std::string> path;
    std::string method;

    explicit Stmt(K k) : kind(k) {}
};

struct Block {
    std::vector<Stmt*> stats;
};

struct Chunk {
    Block* root = nullptr;
};

inline const char* soSpell(SO op) {
    switch (op) {
        case SO::Add: return "+";
        case SO::Sub: return "-";
        case SO::Mul: return "*";
        case SO::Div: return "/";
        case SO::Mod: return "%";
        case SO::Pow: return "^";
        case SO::Concat: return "..";
        case SO::Eq: return "==";
        case SO::Ne: return "~=";
        case SO::Lt: return "<";
        case SO::Le: return "<=";
        case SO::Gt: return ">";
        case SO::Ge: return ">=";
        case SO::And: return "and";
        case SO::Or: return "or";
        default: return "?";
    }
}

}
}
