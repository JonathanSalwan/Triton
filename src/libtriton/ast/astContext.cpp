//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace ast {

    AstContext::AstContext(const triton::modes::Modes& modes) : astGarbageCollector(modes) {
    }


    AbstractNode* AstContext::bv(triton::uint512 value, triton::uint32 size) {
      AbstractNode* node = new(std::nothrow) BvNode(value, size, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvadd(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvaddNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvandNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvashr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvashrNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvfalse(void) {
      AbstractNode* node = new(std::nothrow) BvNode(0, 1, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvlshr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvlshrNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvmul(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvmulNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvnand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvnandNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvneg(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvnegNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvnorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvnot(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvnotNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvrol(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrolNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvrol(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrolNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvror(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrorNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvror(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrorNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsdiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsdivNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsgeNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsgt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsgtNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvshl(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvshlNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsle(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsleNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvslt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsltNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsmod(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsmodNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsrem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsremNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvsub(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsubNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvtrue(void) {
      AbstractNode* node = new(std::nothrow) BvNode(1, 1, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvudiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvudivNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvuge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvugeNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvugt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvugtNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvule(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvuleNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvult(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvultNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvurem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvuremNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


     AbstractNode* AstContext::bvxnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvxnorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::bvxor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvxorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::concat(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) ConcatNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    template AbstractNode* AstContext::concat(const std::vector<AbstractNode*>& exprs);
    template AbstractNode* AstContext::concat(const std::list<AbstractNode*>& exprs);
    template <typename T>
    AbstractNode* AstContext::concat(const T& exprs) {
      AbstractNode* node = new(std::nothrow) ConcatNode(exprs, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::decimal(triton::uint512 value) {
      AbstractNode* node = new(std::nothrow) DecimalNode(value, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::distinct(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) DistinctNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::equal(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) EqualNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr) {
      /* Optimization: If we extract the full size of expr, just return expr */
      if (low == 0 && (high + 1) == expr->getBitvectorSize())
        return expr;

      AbstractNode* node = new(std::nothrow) ExtractNode(high, low, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr) {
      AbstractNode* node = new(std::nothrow) IteNode(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::land(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) LandNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    template AbstractNode* AstContext::land(const std::vector<AbstractNode*>& exprs);
    template AbstractNode* AstContext::land(const std::list<AbstractNode*>& exprs);
    template <typename T>
    AbstractNode* AstContext::land(const T& exprs) {
      AbstractNode* node = new(std::nothrow) LandNode(exprs, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::let(std::string alias, AbstractNode* expr2, AbstractNode* expr3) {
      AbstractNode* node = new(std::nothrow) LetNode(alias, expr2, expr3);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::lnot(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) LnotNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::lor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) LorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    template AbstractNode* AstContext::lor(const std::vector<AbstractNode*>& exprs);
    template AbstractNode* AstContext::lor(const std::list<AbstractNode*>& exprs);
    template <typename T>
    AbstractNode* AstContext::lor(const T& exprs) {
      AbstractNode* node = new(std::nothrow) LorNode(exprs, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::reference(triton::engines::symbolic::SymbolicExpression& expr) {
      AbstractNode* node = new(std::nothrow) ReferenceNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::string(std::string value) {
      AbstractNode* node = new(std::nothrow) StringNode(value, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::sx(triton::uint32 sizeExt, AbstractNode* expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      AbstractNode* node = new(std::nothrow) SxNode(sizeExt, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return this->astGarbageCollector.recordAstNode(node);
    }


    AbstractNode* AstContext::variable(triton::engines::symbolic::SymbolicVariable& symVar) {
      AbstractNode* ret  = nullptr;
      AbstractNode* node = new(std::nothrow) VariableNode(symVar, *this);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      ret = this->astGarbageCollector.recordAstNode(node);
      this->astGarbageCollector.recordVariableAstNode(symVar.getName(), ret);

      return ret;
    }


    AbstractNode* AstContext::zx(triton::uint32 sizeExt, AbstractNode* expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      AbstractNode* node = new(std::nothrow) ZxNode(sizeExt, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return this->astGarbageCollector.recordAstNode(node);
    }


    triton::ast::AstGarbageCollector& AstContext::getAstGarbageCollector(void) {
      return this->astGarbageCollector;
    }


    const triton::ast::AstGarbageCollector& AstContext::getAstGarbageCollector(void) const {
      return this->astGarbageCollector;
    }


    void AstContext::initVariable(const std::string& name, const triton::uint512& value) {
      this->valueMapping.insert(std::make_pair(name, value));
    }


    void AstContext::updateVariable(const std::string& name, const triton::uint512& value) {
      for (auto& kv: this->astGarbageCollector.getAstVariableNodes()) {
        if (kv.first == name) {
          assert(kv.second->getType() == triton::ast::VARIABLE_NODE);
          this->valueMapping[dynamic_cast<VariableNode*>(kv.second)->getVar().getName()] = value;
          kv.second->init();
          return;
        }
      }
      throw triton::exceptions::Ast("AstContext::updateVariable(): Variable to update not found");
    }


    const triton::uint512& AstContext::getValueForVariable(const std::string& varName) const {
      try {
        return this->valueMapping.at(varName);
      } catch(const std::out_of_range& e) {
        throw triton::exceptions::Ast("AstContext::getValueForVariable(): Variable doesn't exists");
      }
    }

  }; /* ast namespace */
}; /* triton namespace */
