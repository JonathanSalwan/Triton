//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <iosfwd>
#include <string>
#include <sstream>

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicEnums.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/tritonTypes.hpp>



namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicExpression::SymbolicExpression(const triton::ast::SharedAbstractNode& node, triton::usize id, triton::engines::symbolic::expression_e type, const std::string& comment)
        : originMemory(),
          originRegister() {
        this->ast           = node;
        this->comment       = comment;
        this->id            = id;
        this->isTainted     = false;
        this->type          = type;
      }


      SymbolicExpression::SymbolicExpression(const SymbolicExpression& other) {
        this->ast            = other.ast;
        this->comment        = other.comment;
        this->id             = other.id;
        this->isTainted      = other.isTainted;
        this->originMemory   = other.originMemory;
        this->originRegister = other.originRegister;
        this->type           = other.type;
      }


      SymbolicExpression& SymbolicExpression::operator=(const SymbolicExpression& other) {
        this->ast            = other.ast;
        this->comment        = other.comment;
        this->id             = other.id;
        this->isTainted      = other.isTainted;
        this->originMemory   = other.originMemory;
        this->originRegister = other.originRegister;
        this->type           = other.type;
        return *this;
      }


      const triton::ast::SharedAbstractNode& SymbolicExpression::getAst(void) const {
        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getAst(): No AST defined.");
        return this->ast;
      }


      triton::ast::SharedAbstractNode SymbolicExpression::getNewAst(void) const {
        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getNewAst(): No AST defined.");
        return triton::ast::newInstance(this->ast.get());
      }


      const std::string& SymbolicExpression::getComment(void) const {
        return this->comment;
      }


      triton::usize SymbolicExpression::getId(void) const {
        return this->id;
      }


      std::string SymbolicExpression::getFormattedId(void) const {
        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedId(): No AST defined.");

        if (ast->getContext()->getRepresentationMode() == triton::ast::representations::SMT_REPRESENTATION)
          return "ref!" + std::to_string(this->id);

        else if (ast->getContext()->getRepresentationMode() == triton::ast::representations::PYTHON_REPRESENTATION)
          return "ref_" + std::to_string(this->id);

        else
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedId(): Invalid AST representation mode.");
      }


      std::string SymbolicExpression::getFormattedComment(void) const {
        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedComment(): No AST defined.");

        if (this->getComment().empty())
          return "";

        else if (ast->getContext()->getRepresentationMode() == triton::ast::representations::SMT_REPRESENTATION)
          return "; " + this->getComment();

        else if (ast->getContext()->getRepresentationMode() == triton::ast::representations::PYTHON_REPRESENTATION)
          return "# " + this->getComment();

        else
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedComment(): Invalid AST representation mode.");
      }


      std::string SymbolicExpression::getFormattedExpression(void) const {
        std::ostringstream stream;

        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedExpression(): No AST defined.");

        else if (ast->getContext()->getRepresentationMode() == triton::ast::representations::SMT_REPRESENTATION) {
          stream << "(define-fun " << this->getFormattedId() << " () (_ BitVec " << std::dec << this->getAst()->getBitvectorSize() << ") " << this->getAst() << ")";
          if (!this->getComment().empty())
            stream << " " << this->getFormattedComment();
          return stream.str();
        }

        else if (ast->getContext()->getRepresentationMode() == triton::ast::representations::PYTHON_REPRESENTATION) {
          stream << this->getFormattedId() << " = " << this->getAst();
          if (!this->getComment().empty())
            stream << " " << this->getFormattedComment();
          return stream.str();
        }

        else
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedExpression(): Invalid AST representation mode.");
      }


      triton::engines::symbolic::expression_e SymbolicExpression::getType(void) const {
        return this->type;
      }


      const triton::arch::MemoryAccess& SymbolicExpression::getOriginMemory(void) const {
        return this->originMemory;
      }


      const triton::arch::Register& SymbolicExpression::getOriginRegister(void) const {
        return this->originRegister;
      }


      void SymbolicExpression::setAst(const triton::ast::SharedAbstractNode& node) {
        auto old = this->ast;
        if (node == old)
          return;

        if (old) {
          for (auto sp : old->getParents()) {
            node->setParent(sp.get());
          }
        }

        this->ast = node;

        if (!old || !old->canReplaceNodeWithoutUpdate(ast)) {
          this->ast->initParents();
        }

      }


      void SymbolicExpression::setComment(const std::string& comment) {
        this->comment = comment;
      }


      void SymbolicExpression::setType(triton::engines::symbolic::expression_e type) {
        this->type = type;
      }


      void SymbolicExpression::setOriginMemory(const triton::arch::MemoryAccess& mem) {
        this->originMemory = mem;
      }


      void SymbolicExpression::setOriginRegister(const triton::arch::Register& reg) {
        this->originRegister = reg;
      }


      bool SymbolicExpression::isRegister(void) const {
        return (this->type == triton::engines::symbolic::REGISTER_EXPRESSION);
      }


      bool SymbolicExpression::isMemory(void) const {
        return (this->type == triton::engines::symbolic::MEMORY_EXPRESSION);
      }


      bool SymbolicExpression::isSymbolized(void) const {
        if (this->ast == nullptr)
          return false;
        return this->ast->isSymbolized();
      }


      std::ostream& operator<<(std::ostream& stream, const SymbolicExpression& symExpr) {
        stream << symExpr.getFormattedExpression();
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const SymbolicExpression* symExpr) {
        stream << *symExpr;
        return stream;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
