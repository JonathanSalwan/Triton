//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
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
        this->address       = -1;
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
        this->address        = other.address;
      }


      SymbolicExpression& SymbolicExpression::operator=(const SymbolicExpression& other) {
        this->ast            = other.ast;
        this->comment        = other.comment;
        this->id             = other.id;
        this->isTainted      = other.isTainted;
        this->originMemory   = other.originMemory;
        this->originRegister = other.originRegister;
        this->type           = other.type;
        this->address        = other.address;
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

        else if (ast->getContext()->getRepresentationMode() == triton::ast::representations::PCODE_REPRESENTATION) {
          if (this->isMemory()) {
            auto mem = this->getOriginMemory();
            std::ostringstream ss;
            ss << "@[0x" << std::hex << mem.getAddress() << ":" << std::dec << mem.getBitSize() << "]";
            return ss.str();
          }
          else if (this->isRegister()) {
            auto reg = this->getOriginRegister();
            return reg.getName() + "_" + std::to_string(this->id);
          }
          else {
            return "tmp_" + std::to_string(this->id);
          }
        }

        else
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedId(): Invalid AST representation mode.");
      }


      std::string SymbolicExpression::getFormattedComment(void) const {
        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedComment(): No AST defined.");

        if (this->getComment().empty())
          return "";

        switch (ast->getContext()->getRepresentationMode()) {
          case triton::ast::representations::SMT_REPRESENTATION:
          case triton::ast::representations::PCODE_REPRESENTATION:
            return "; " + this->getComment();

          case triton::ast::representations::PYTHON_REPRESENTATION:
            return "# " + this->getComment();

          default:
            throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedComment(): Invalid AST representation mode.");
        };
      }


      std::string SymbolicExpression::getBitvectorDefine(void) const {
        std::ostringstream stream;
        stream << "(define-fun " << this->getFormattedId() << " () (_ BitVec " << std::dec << this->getAst()->getBitvectorSize() << ") " << this->getAst() << ")";
        return stream.str();
      }


      std::string SymbolicExpression::getArrayDefine(void) const {
        std::ostringstream stream;

        if (this->getAst()->getType() == triton::ast::ARRAY_NODE) {
          stream << "(declare-fun " << this->getFormattedId() << " () (Array (_ BitVec " << std::dec << triton::ast::getIndexSize(this->getAst()) << ") (_ BitVec 8)))";
        }
        else {
          stream << "(define-fun " << this->getFormattedId() << " () (Array (_ BitVec " << std::dec << triton::ast::getIndexSize(this->getAst()) << ") (_ BitVec 8)) " << this->getAst() << ")";
        }

        return stream.str();
      }


      std::string SymbolicExpression::getFormattedExpression(void) const {
        std::ostringstream stream;

        if (this->ast == nullptr)
          throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedExpression(): No AST defined.");

        switch (ast->getContext()->getRepresentationMode()) {
          case triton::ast::representations::SMT_REPRESENTATION:
            stream << (this->getAst()->isArray() ? this->getArrayDefine() : this->getBitvectorDefine());
            break;
          case triton::ast::representations::PCODE_REPRESENTATION:
          case triton::ast::representations::PYTHON_REPRESENTATION:
            stream << this->getFormattedId() << " = " << this->getAst();
            break;

          default:
            throw triton::exceptions::SymbolicExpression("SymbolicExpression::getFormattedExpression(): Invalid AST representation mode.");
        }

        if (!this->getComment().empty()) {
          stream << " " << this->getFormattedComment();
        }

        return stream.str();
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
        triton::ast::SharedAbstractNode old = this->ast;

        /* If node is the same as the old one, just do not set the ast. */
        if (node == old)
          return;

        if (old) {
          /* Link old parents with the new node */
          for (auto sp : old->getParents()) {
            node->setParent(sp.get());
          }
        }

        /* Set the new ast */
        this->ast = node;

        /* Do not init parents if the new node has same properties that the old one */
        if (!old || !old->canReplaceNodeWithoutUpdate(ast)) {
          this->ast->initParents();
        }
      }


      void SymbolicExpression::setComment(const std::string& comment) {
        this->comment = comment;
      }


      void SymbolicExpression::setAddress(triton::uint64 address) {
        this->address = address;
      }


      triton::uint64 SymbolicExpression::getAddress(void) const {
        return this->address;
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


      void SymbolicExpression::writeBackDisassembly(const std::string& disassembly) {
        this->disassembly = disassembly;
      }


      const std::string& SymbolicExpression::getDisassembly(void) {
        return this->disassembly;
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
