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


    SharedAbstractNode AstContext::bv(triton::uint512 value, triton::uint32 size) {
      SharedAbstractNode node = std::shared_ptr<BvNode>(new(std::nothrow) BvNode(value, size, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvadd(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvaddNode>(new(std::nothrow) BvaddNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvandNode>(new(std::nothrow) BvandNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvashr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvashrNode>(new(std::nothrow) BvashrNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvfalse(void) {
      SharedAbstractNode node = std::shared_ptr<BvNode>(new(std::nothrow) BvNode(0, 1, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvlshr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvlshrNode>(new(std::nothrow) BvlshrNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvmul(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvmulNode>(new(std::nothrow) BvmulNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvnand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvnandNode>(new(std::nothrow) BvnandNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvneg(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<BvnegNode>(new(std::nothrow) BvnegNode(expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvnorNode>(new(std::nothrow) BvnorNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvnot(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<BvnotNode>(new(std::nothrow) BvnotNode(expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvorNode>(new(std::nothrow) BvorNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvrol(triton::uint32 rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<BvrolNode>(new(std::nothrow) BvrolNode(rot, expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvrol(const SharedAbstractNode& rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<BvrolNode>(new(std::nothrow) BvrolNode(rot, expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvror(triton::uint32 rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<BvrorNode>(new(std::nothrow) BvrorNode(rot, expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvror(const SharedAbstractNode& rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<BvrorNode>(new(std::nothrow) BvrorNode(rot, expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsdiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsdivNode>(new(std::nothrow) BvsdivNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsgeNode>(new(std::nothrow) BvsgeNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsgt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsgtNode>(new(std::nothrow) BvsgtNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvshl(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvshlNode>(new(std::nothrow) BvshlNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsle(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsleNode>(new(std::nothrow) BvsleNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvslt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsltNode>(new(std::nothrow) BvsltNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsmod(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsmodNode>(new(std::nothrow) BvsmodNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsrem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsremNode>(new(std::nothrow) BvsremNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvsub(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvsubNode>(new(std::nothrow) BvsubNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvtrue(void) {
      SharedAbstractNode node = std::shared_ptr<BvNode>(new(std::nothrow) BvNode(1, 1, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvudiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvudivNode>(new(std::nothrow) BvudivNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvuge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvugeNode>(new(std::nothrow) BvugeNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvugt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvugtNode>(new(std::nothrow) BvugtNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvule(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvuleNode>(new(std::nothrow) BvuleNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvult(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvultNode>(new(std::nothrow) BvultNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvurem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvuremNode>(new(std::nothrow) BvuremNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


     SharedAbstractNode AstContext::bvxnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvxnorNode>(new(std::nothrow) BvxnorNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::bvxor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<BvxorNode>(new(std::nothrow) BvxorNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::concat(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<ConcatNode>(new(std::nothrow) ConcatNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::concat(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::concat(const std::list<SharedAbstractNode>& exprs);
    template <typename T>
    SharedAbstractNode AstContext::concat(const T& exprs) {
      SharedAbstractNode node = std::shared_ptr<ConcatNode>(new(std::nothrow) ConcatNode(exprs, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::decimal(triton::uint512 value) {
      SharedAbstractNode node = std::shared_ptr<DecimalNode>(new(std::nothrow) DecimalNode(value, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::distinct(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<DistinctNode>(new(std::nothrow) DistinctNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::equal(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<EqualNode>(new(std::nothrow) EqualNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::extract(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr) {
      /* Optimization: If we extract the full size of expr, just return expr */
      if (low == 0 && (high + 1) == expr->getBitvectorSize())
        return expr;

      SharedAbstractNode node = std::shared_ptr<ExtractNode>(new(std::nothrow) ExtractNode(high, low, expr));

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return node;
    }


    SharedAbstractNode AstContext::ite(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr) {
      SharedAbstractNode node = std::shared_ptr<IteNode>(new(std::nothrow) IteNode(ifExpr, thenExpr, elseExpr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::land(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<LandNode>(new(std::nothrow) LandNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::land(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::land(const std::list<SharedAbstractNode>& exprs);
    template <typename T>
    SharedAbstractNode AstContext::land(const T& exprs) {
      SharedAbstractNode node = std::shared_ptr<LandNode>(new(std::nothrow) LandNode(exprs, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::let(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3) {
      SharedAbstractNode node = std::shared_ptr<LetNode>(new(std::nothrow) LetNode(alias, expr2, expr3));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::lnot(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::shared_ptr<LnotNode>(new(std::nothrow) LnotNode(expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::lor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::shared_ptr<LorNode>(new(std::nothrow) LorNode(expr1, expr2));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::lor(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::lor(const std::list<SharedAbstractNode>& exprs);
    template <typename T>
    SharedAbstractNode AstContext::lor(const T& exprs) {
      SharedAbstractNode node = std::shared_ptr<LorNode>(new(std::nothrow) LorNode(exprs, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::reference(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
      SharedAbstractNode node = std::shared_ptr<ReferenceNode>(new(std::nothrow) ReferenceNode(expr));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::string(std::string value) {
      SharedAbstractNode node = std::shared_ptr<StringNode>(new(std::nothrow) StringNode(value, *this));
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      return node;
    }


    SharedAbstractNode AstContext::sx(triton::uint32 sizeExt, const SharedAbstractNode& expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      SharedAbstractNode node = std::shared_ptr<SxNode>(new(std::nothrow) SxNode(sizeExt, expr));

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return node;
    }


    SharedAbstractNode AstContext::variable(triton::engines::symbolic::SymbolicVariable& symVar) {
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
        SharedAbstractNode node = std::shared_ptr<VariableNode>(new(std::nothrow) VariableNode(symVar, *this));
        if (node == nullptr)
          throw triton::exceptions::Ast("Node builders - Not enough memory");
        return node;
      }
    }


    SharedAbstractNode AstContext::zx(triton::uint32 sizeExt, const SharedAbstractNode& expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      SharedAbstractNode node = std::shared_ptr<ZxNode>(new(std::nothrow) ZxNode(sizeExt, expr));

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      return node;
    }


    void AstContext::initVariable(const std::string& name, const triton::uint512& value, const SharedAbstractNode& node) {
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


    SharedAbstractNode AstContext::getVariableNode(const std::string& name) {
      auto it = this->valueMapping.find(name);
      if (it == this->valueMapping.end())
        return nullptr;
      else
        return it->second.first;
    }


    const triton::uint512& AstContext::getVariableValue(const std::string& varName) const {
      try {
        return this->valueMapping.at(varName).second;
      } catch (const std::out_of_range&) {
        throw triton::exceptions::Ast("AstContext::getVariableValue(): Variable doesn't exists");
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
