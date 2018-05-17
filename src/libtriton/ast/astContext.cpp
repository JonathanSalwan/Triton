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

    AstContext::AstContext() {
    }


    AstContext::AstContext(const AstContext& other)
      : astRepresentation(other.astRepresentation),
        valueMapping(other.valueMapping) {
    }


    AstContext& AstContext::operator=(const AstContext& other) {
      this->astRepresentation = other.astRepresentation;
      this->valueMapping = other.valueMapping;
      return *this;
    }


    AbstractNode* AstContext::bv(triton::uint512 value, triton::uint32 size) {
      AbstractNode* node = new(std::nothrow) BvNode(value, size, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvadd(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvaddNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvandNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvashr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvashrNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvfalse(void) {
      AbstractNode* node = new(std::nothrow) BvNode(0, 1, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvlshr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvlshrNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvmul(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvmulNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvnand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvnandNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvneg(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvnegNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvnorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvnot(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvnotNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvrol(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrolNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvrol(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrolNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvror(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrorNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvror(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrorNode(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsdiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsdivNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsgeNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsgt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsgtNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvshl(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvshlNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsle(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsleNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvslt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsltNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsmod(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsmodNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsrem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsremNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvsub(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsubNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvtrue(void) {
      AbstractNode* node = new(std::nothrow) BvNode(1, 1, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvudiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvudivNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvuge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvugeNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvugt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvugtNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvule(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvuleNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvult(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvultNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvurem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvuremNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


     AbstractNode* AstContext::bvxnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvxnorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::bvxor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvxorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::concat(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) ConcatNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    template TRITON_EXPORT AbstractNode* AstContext::concat(const std::vector<AbstractNode*>& exprs);
    template TRITON_EXPORT AbstractNode* AstContext::concat(const std::list<AbstractNode*>& exprs);
    template <typename T>
    AbstractNode* AstContext::concat(const T& exprs) {
      AbstractNode* node = new(std::nothrow) ConcatNode(exprs, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::decimal(triton::uint512 value) {
      AbstractNode* node = new(std::nothrow) DecimalNode(value, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::distinct(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) DistinctNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::equal(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) EqualNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr) {
      /* Optimization: If we extract the full size of expr, just return expr */
      if (low == 0 && (high + 1) == expr->getBitvectorSize())
        return expr;

      AbstractNode* node = new(std::nothrow) ExtractNode(high, low, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return node;
    }


    AbstractNode* AstContext::ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr) {
      AbstractNode* node = new(std::nothrow) IteNode(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::land(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) LandNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    template TRITON_EXPORT AbstractNode* AstContext::land(const std::vector<AbstractNode*>& exprs);
    template TRITON_EXPORT AbstractNode* AstContext::land(const std::list<AbstractNode*>& exprs);
    template <typename T>
    AbstractNode* AstContext::land(const T& exprs) {
      AbstractNode* node = new(std::nothrow) LandNode(exprs, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::let(std::string alias, AbstractNode* expr2, AbstractNode* expr3) {
      AbstractNode* node = new(std::nothrow) LetNode(alias, expr2, expr3);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::lnot(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) LnotNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::lor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) LorNode(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    template TRITON_EXPORT AbstractNode* AstContext::lor(const std::vector<AbstractNode*>& exprs);
    template TRITON_EXPORT AbstractNode* AstContext::lor(const std::list<AbstractNode*>& exprs);
    template <typename T>
    AbstractNode* AstContext::lor(const T& exprs) {
      AbstractNode* node = new(std::nothrow) LorNode(exprs, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::reference(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
      AbstractNode* node = new(std::nothrow) ReferenceNode(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::string(std::string value) {
      AbstractNode* node = new(std::nothrow) StringNode(value, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    AbstractNode* AstContext::sx(triton::uint32 sizeExt, AbstractNode* expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      AbstractNode* node = new(std::nothrow) SxNode(sizeExt, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return node;
    }


    AbstractNode* AstContext::variable(triton::engines::symbolic::SymbolicVariable& symVar) {
      // try to get node from variable pool
      auto it = this->valueMapping.find(symVar.getName());
      if (it != this->valueMapping.end()) {
        auto& node = it->second.first;

        if (node->getBitvectorSize() != symVar.getSize())
          throw triton::exceptions::Ast("Node builders - Missmatching variable size.");

        // This node already exist, just return it
        return node;
      } else {
        // if not found, create a new variable node
        AbstractNode* node = new(std::nothrow) VariableNode(symVar, *this);
        if (node == nullptr)
          throw triton::exceptions::Ast("Node builders - Not enough memory");
        return node;
      }
    }


    AbstractNode* AstContext::zx(triton::uint32 sizeExt, AbstractNode* expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      AbstractNode* node = new(std::nothrow) ZxNode(sizeExt, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return node;
    }


    void AstContext::initVariable(const std::string& name, const triton::uint512& value, AbstractNode* node) {
      // FIXME: Use insert and check result
      auto it = this->valueMapping.find(name);
      if (it == this->valueMapping.end())
        this->valueMapping.insert(std::make_pair(name, std::make_pair(node, value)));
      else
        throw triton::exceptions::Ast("Ast variable already initialized");
    }


    void AstContext::updateVariable(const std::string& name, const triton::uint512& value) {
      auto& kv = this->valueMapping.at(name);
      kv.second = value;
      kv.first->init();
    }


    AbstractNode* AstContext::getVariableNode(const std::string& name) {
      auto it = this->valueMapping.find(name);
      if (it == this->valueMapping.end())
        return nullptr;
      else
        return it->second.first;
    }


    const triton::uint512& AstContext::getValueForVariable(const std::string& varName) const {
      try {
        return this->valueMapping.at(varName).second;
      } catch (const std::out_of_range&) {
        throw triton::exceptions::Ast("AstContext::getValueForVariable(): Variable doesn't exists");
      }
    }


    void AstContext::setRepresentationMode(triton::uint32 mode) {
      this->astRepresentation.setMode(mode);
    }


    triton::uint32 AstContext::getRepresentationMode(void) const {
      return this->astRepresentation.getMode();
    }


    std::ostream& AstContext::print(std::ostream& stream, AbstractNode* node) {
      return this->astRepresentation.print(stream, node);
    }

  }; /* ast namespace */
}; /* triton namespace */
