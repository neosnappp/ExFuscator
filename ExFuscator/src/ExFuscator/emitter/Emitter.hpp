#pragma once

#include "astra/parser/Ast.hpp"

namespace astra {

class Emitter {
public:
    std::string emit(const ast::Chunk& chunk);

private:
    std::string out_;

    void block(const ast::Block* b);
    void stmt(const ast::Stmt* s);
    void expr(const ast::Expr* e, int limit);
    void rawExpr(const ast::Expr* e);
    void funcBody(const ast::FuncLit* f, bool skipSelf = false);
    void args(const std::vector<ast::Expr*>& v);
    void exprList(const std::vector<ast::Expr*>& v);
    void stringLiteral(const std::string& bytes);

    bool needsParens(const ast::Expr* e, int limit) const;

    static bool isSuffixed(const ast::Expr* e);
    static std::pair<int, int> binPrio(ast::SO op);
};

}
