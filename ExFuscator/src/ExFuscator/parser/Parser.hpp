#pragma once

#include "astra/lexer/Token.hpp"
#include "astra/parser/Ast.hpp"

namespace astra {

class Parser {
public:
    Parser(std::vector<Token> toks);

    ast::Chunk parse();

private:

    std::vector<std::unique_ptr<ast::Expr>> exprArena_;
    std::vector<std::unique_ptr<ast::Stmt>> stmtArena_;
    std::vector<std::unique_ptr<ast::Block>> blockArena_;
    std::vector<std::unique_ptr<ast::FuncLit>> funcArena_;

    ast::Expr* mkExpr(ast::EK k, int line);
    ast::Stmt* mkStmt(ast::Stmt::K k, int line);
    ast::Block* mkBlock();
    ast::FuncLit* mkFunc(int line);

    std::vector<Token> toks_;
    size_t p_ = 0;

    const Token& peek(size_t off = 0) const;
    const Token& advance();
    bool check(TokType t) const;
    bool checkKw(const char* kw) const;
    bool checkOp(const char* op) const;
    bool accept(TokType t);
    bool acceptKw(const char* kw);
    bool acceptOp(const char* op);
    const Token& expect(TokType t, const char* what);
    std::string expectName(const char* what);
    void expectOp(const char* op);
    void expectKw(const char* kw);
    [[noreturn]] void fail(const std::string& msg);

    static constexpr int kMaxNest = 400;

    static constexpr int kMaxLocals = 200;

    int nest_ = 0;
    std::vector<int> fnLocals_;

    struct NestGuard {
        Parser* p;
        explicit NestGuard(Parser* pp) : p(pp) {
            if (p->nest_ >= kMaxNest)
                p->fail("chunk has too many syntax levels");
            ++p->nest_;
        }
        ~NestGuard() { --p->nest_; }
    };

    void enterFn() { fnLocals_.push_back(0); }
    void exitFn() { if (!fnLocals_.empty()) fnLocals_.pop_back(); }
    void addLocals(int n);

    static bool isCompoundOp(const Token& t, ast::SO& out);

    ast::Block* parseBlock();
    ast::Stmt* parseStatement();
    ast::Stmt* parseIf();
    ast::Stmt* parseNumericFor(const std::string& name);
    ast::Stmt* parseGenericFor(const std::string& first);
    ast::Stmt* parseFuncStatement();
    ast::Stmt* parseLocal();

    std::vector<std::string> parseNameList(const char* what);
    void parseNameAttributes();
    void skipTypeAnnotation();

    ast::Expr* buildInterpString(const Token& t);
    ast::Expr* parseIfExpression(int line);
    ast::Expr* parseInterpExprText(const std::string& src, int line);

    ast::Expr* parseSuffixed();
    ast::Expr* parsePrimary();
    ast::Expr* parseExpr(int limit);
    ast::Expr* parseExpr() { return parseExpr(0); }
    ast::Expr* parseSimpleExpr();
    ast::Expr* parseUnary();
    ast::FuncLit* parseFuncBody(int line);
    std::vector<ast::Expr*> parseExprList();
    std::vector<ast::Expr*> parseCallArgs(ast::Expr* callee);
    ast::Expr* parseTableConstructor();
    ast::Expr* cloneForCompound(ast::Expr* e, bool paren = false);
};

}
