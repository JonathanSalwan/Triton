//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include "triton/symbolicEnums.hpp"       // for symkind_e, symkind_e::MEM
#include "tritoncore/types.hpp"         // for usize
#include <triton/exceptions.hpp>          // for SymbolicValue
#include <triton/symbolicValue.hpp>  // for SymbolicValue

#include "tritonast/nodes.hpp"                 // for AbstractNode, newInstance

#include <iosfwd>                         // for ostream
#include <string>                         // for string

namespace triton {
  namespace engines {
    namespace symbolic {

      SymbolicValue::SymbolicValue(triton::ast::SharedAbstractNode node, triton::usize id, symkind_e kind, const std::string& comment):
        kind(kind),
        ast(std::move(node)),
        comment(comment),
        id(id)
        {
          if(ast == nullptr)
            throw triton::exceptions::SymbolicVariable("SymbolicValue(): No AST defined.");
        }


      triton::usize SymbolicValue::getId(void) const {
        return this->id;
      }

      bool SymbolicValue::isRegister(void) const {
        return (this->kind == triton::engines::symbolic::REG);
      }


      bool SymbolicValue::isMemory(void) const {
        return (this->kind == triton::engines::symbolic::MEM);
      }


      bool SymbolicValue::isSymbolized(void) const {
        return this->ast->isSymbolized();
      }


      symkind_e SymbolicValue::getKind(void) const {
        return this->kind;
      }


      void SymbolicValue::setKind(symkind_e k) {
        this->kind = k;
      }


      const std::string& SymbolicValue::getComment(void) const {
        return this->comment;
      }


      void SymbolicValue::setComment(const std::string& comment) {
        this->comment = comment;
      }


      triton::ast::AbstractNode* SymbolicValue::getAst(void) const {
        return this->ast.get();
      }

      triton::ast::SharedAbstractNode const& SymbolicValue::getShareAst(void) {
        return this->ast;
      }


      triton::ast::SharedAbstractNode SymbolicValue::getNewAst(void) const {
        return triton::ast::newInstance(this->ast.get());
      }


      void SymbolicValue::setAst(triton::ast::SharedAbstractNode const& node) {
        if(node == nullptr)
          throw triton::exceptions::SymbolicVariable("SymbolicValue::setAst(): No AST defined.");

        for(auto sp: this->ast->getParents()) {
          node->setParent(sp.get());
        }
        this->ast = node;
        this->ast->init();
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

