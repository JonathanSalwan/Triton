//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <symbolicExpression.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicExpression::SymbolicExpression(smt2lib::smtAstAbstractNode* node, triton::__uint id, symkind_e kind) {
        this->ast         = node;
        this->id          = id;
        this->isTainted   = false;
        this->kind        = kind;
      }


      SymbolicExpression::SymbolicExpression(smt2lib::smtAstAbstractNode* node, triton::__uint id, symkind_e kind, std::string comment) {
        this->comment     = comment;
        this->ast         = node;
        this->id          = id;
        this->isTainted   = false;
        this->kind        = kind;
      }


      SymbolicExpression::~SymbolicExpression() {
      }


      /* Returns the SMT AST expression of the symbolic expression */
      smt2lib::smtAstAbstractNode* SymbolicExpression::getAst(void) {
        if (this->ast == nullptr)
          throw std::runtime_error("SymbolicExpression::getAst(): No AST defined.");
        return this->ast;
      }


      /* Returns a new SMT AST expression of the symbolic expression */
      smt2lib::smtAstAbstractNode* SymbolicExpression::getNewAst(void) {
        if (this->ast == nullptr)
          throw std::runtime_error("SymbolicExpression::getNewAst(): No AST defined.");
        return smt2lib::newInstance(this->ast);
      }


      /* Returns the comment of the expression */
      std::string SymbolicExpression::getComment(void) {
        return this->comment;
      }


      /* Returns the ID of the symbolic expression */
      triton::__uint SymbolicExpression::getId(void) {
        return this->id;
      }


      /* Returns a std::string ID of the symbolic expression */
      std::string SymbolicExpression::getId2Str(void) {
        return "#" + std::to_string(this->id);
      }


      /* Set the destination expression */
      void SymbolicExpression::setAst(smt2lib::smtAstAbstractNode* node) {
        this->ast = node;
      }


      symkind_e SymbolicExpression::getKind(void) {
        return this->kind;
      }


      void SymbolicExpression::setKind(symkind_e k) {
        this->kind = k;
      }


      bool SymbolicExpression::isReg(void) {
        return (this->kind == triton::engines::symbolic::REG);
      }


      bool SymbolicExpression::isMem(void) {
        return (this->kind == triton::engines::symbolic::MEM);
      }


      std::ostream &operator<<(std::ostream &stream, SymbolicExpression symExpr) {
        stream << symExpr.getId2Str() << " = " << symExpr.getAst();
        if (!symExpr.getComment().empty())
          stream << " ; " << symExpr.getComment();
        return stream;
      }


      std::ostream &operator<<(std::ostream &stream, SymbolicExpression* symExpr) {
        stream << symExpr->getId2Str() << " = " << symExpr->getAst();
        if (!symExpr->getComment().empty())
          stream << " ; " << symExpr->getComment();
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

