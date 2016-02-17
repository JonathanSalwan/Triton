//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <api.hpp>
#include <astRepresentation.hpp>
#include <symbolicExpression.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicExpression::SymbolicExpression(triton::ast::AbstractNode* node, triton::__uint id, symkind_e kind, std::string comment) : originRegister() {
        this->comment       = comment;
        this->ast           = node;
        this->id            = id;
        this->isTainted     = false;
        this->kind          = kind;
        this->originAddress = 0;
      }


      SymbolicExpression::~SymbolicExpression() {
      }


      triton::ast::AbstractNode* SymbolicExpression::getAst(void) {
        if (this->ast == nullptr)
          throw std::runtime_error("SymbolicExpression::getAst(): No AST defined.");
        return this->ast;
      }


      triton::ast::AbstractNode* SymbolicExpression::getNewAst(void) {
        if (this->ast == nullptr)
          throw std::runtime_error("SymbolicExpression::getNewAst(): No AST defined.");
        return triton::ast::newInstance(this->ast);
      }


      std::string SymbolicExpression::getComment(void) {
        return this->comment;
      }


      triton::__uint SymbolicExpression::getId(void) {
        return this->id;
      }


      std::string SymbolicExpression::getId2Str(void) {
        if (triton::api.getAstRepresentationMode() == triton::ast::representation::SMT_REPRESENTATION)
          return "ref!" + std::to_string(this->id);

        else if (triton::api.getAstRepresentationMode() == triton::ast::representation::PYTHON_REPRESENTATION)
          return "ref_" + std::to_string(this->id);

        else
          throw std::runtime_error("SymbolicExpression::getId2Str(): Invalid AST representation mode.");
      }


      symkind_e SymbolicExpression::getKind(void) {
        return this->kind;
      }


      triton::__uint SymbolicExpression::getOriginAddress(void) {
        return this->originAddress;
      }


      triton::arch::RegisterOperand& SymbolicExpression::getOriginRegister(void) {
        return this->originRegister;
      }


      void SymbolicExpression::setAst(triton::ast::AbstractNode* node) {
        this->ast = node;
      }


      void SymbolicExpression::setKind(symkind_e k) {
        this->kind = k;
      }


      void SymbolicExpression::setOriginAddress(triton::__uint addr) {
        this->originAddress = addr;
      }


      void SymbolicExpression::setOriginRegister(triton::arch::RegisterOperand& reg) {
        this->originRegister = reg;
      }


      bool SymbolicExpression::isRegister(void) {
        return (this->kind == triton::engines::symbolic::REG);
      }


      bool SymbolicExpression::isMemory(void) {
        return (this->kind == triton::engines::symbolic::MEM);
      }


      std::ostream& operator<<(std::ostream& stream, SymbolicExpression symExpr) {
        stream << symExpr.getId2Str() << " = " << symExpr.getAst();
        if (!symExpr.getComment().empty())
          stream << " ; " << symExpr.getComment();
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, SymbolicExpression* symExpr) {
        stream << *symExpr;
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

