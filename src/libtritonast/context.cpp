//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <tritonast/context.hpp>
#include <tritonast/exceptions.hpp>
#include <tritonast/nodes.hpp>



namespace triton {
  namespace ast {

    SharedAbstractNode Context::bv(triton::uint512 value, triton::uint32 size) {
      return BvNode::create(value, size, *this);
    }

    SharedAbstractNode Context::bvadd(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvaddNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvand(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvandNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvashr(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvashrNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvfalse(void) {
      return this->bv(0, 1);
    }

    SharedAbstractNode Context::bvlshr(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvlshrNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvmul(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvmulNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvnand(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvnandNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvneg(SharedAbstractNode expr) {
      return BvnegNode::create(expr);
    }

    SharedAbstractNode Context::bvnor(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvnorNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvnot(SharedAbstractNode expr) {
      return BvnotNode::create(expr);
    }

    SharedAbstractNode Context::bvor(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvorNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvrol(triton::uint32 rot, SharedAbstractNode expr) {
      return BvrolNode::create(rot, expr);
    }

    SharedAbstractNode Context::bvrol(SharedAbstractNode rot, SharedAbstractNode expr) {
      return BvrolNode::create(rot, expr);
    }

    SharedAbstractNode Context::bvror(triton::uint32 rot, SharedAbstractNode expr) {
      return BvrorNode::create(rot, expr);
    }

    SharedAbstractNode Context::bvror(SharedAbstractNode rot, SharedAbstractNode expr) {
      return BvrorNode::create(rot, expr);
    }

    SharedAbstractNode Context::bvsdiv(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsdivNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvsge(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsgeNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvsgt(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsgtNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvshl(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvshlNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvsle(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsleNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvslt(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsltNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvsmod(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsmodNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvsrem(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsremNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvsub(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvsubNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvtrue(void) {
      return this->bv(1, 1);
    }

    SharedAbstractNode Context::bvudiv(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvudivNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvuge(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvugeNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvugt(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvugtNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvule(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvuleNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvult(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvultNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvurem(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvuremNode::create(expr1, expr2);
    }

     SharedAbstractNode Context::bvxnor(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvxnorNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::bvxor(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return BvxorNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::concat(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return ConcatNode::create(expr1, expr2);
    }

    template SharedAbstractNode Context::concat(const std::vector<SharedAbstractNode>& exprs);
    template SharedAbstractNode Context::concat(const std::list<SharedAbstractNode>& exprs);
    template <typename T>
    SharedAbstractNode Context::concat(const T& exprs) {
      return ConcatNode::create(exprs, *this);
    }

    SharedAbstractNode Context::decimal(triton::uint512 value) {
      return DecimalNode::create(value, *this);
    }

    SharedAbstractNode Context::distinct(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return DistinctNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::equal(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return EqualNode::create(expr1, expr2);
    }

    SharedAbstractNode Context::extract(triton::uint32 high, triton::uint32 low, SharedAbstractNode expr) {
      /* Optimization: If we extract the full size of expr, just return expr */
      if (low == 0 && (high + 1) == expr->getBitvectorSize())
        return expr;

      return ExtractNode::create(high, low, expr);
    }

    SharedAbstractNode Context::ite(SharedAbstractNode ifExpr, SharedAbstractNode thenExpr, SharedAbstractNode elseExpr) {
      return IteNode::create(ifExpr, thenExpr, elseExpr);
    }

    SharedAbstractNode Context::land(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return LandNode::create(expr1, expr2);
    }

    template SharedAbstractNode Context::land(const std::vector<SharedAbstractNode>& exprs);
    template SharedAbstractNode Context::land(const std::list<SharedAbstractNode>& exprs);
    template <typename T>
    SharedAbstractNode Context::land(const T& exprs) {
      return LandNode::create(exprs, *this);
    }

    SharedAbstractNode Context::let(std::string alias, SharedAbstractNode expr2, SharedAbstractNode expr3) {
      return LetNode::create(alias, expr2, expr3);
    }

    SharedAbstractNode Context::lnot(SharedAbstractNode expr) {
      return LnotNode::create(expr);
    }

    SharedAbstractNode Context::lor(SharedAbstractNode expr1, SharedAbstractNode expr2) {
      return LorNode::create(expr1, expr2);
    }

    template SharedAbstractNode Context::lor(const std::vector<SharedAbstractNode>& exprs);
    template SharedAbstractNode Context::lor(const std::list<SharedAbstractNode>& exprs);
    template <typename T>
    SharedAbstractNode Context::lor(const T& exprs) {
      return LorNode::create(exprs, *this);
    }

    SharedAbstractNode Context::reference(SharedAbstractNode ast, size_t id, std::function<void()> const& end) {
      return ReferenceNode::create(ast, id, end);
    }

    SharedAbstractNode Context::string(std::string value) {
      return StringNode::create(value, *this);
    }

    SharedAbstractNode Context::sx(triton::uint32 sizeExt, SharedAbstractNode expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      return SxNode::create(sizeExt, expr);
    }

    SharedAbstractNode Context::variable(std::string const& varName, triton::uint32 size) {

      // try to get node from variable pool
      auto it = this->valueMapping.find(varName);
      if(it != this->valueMapping.end()) {
        auto& node = it->second.first;

        if(node->getBitvectorSize() != size)
          throw triton::ast::exceptions::Ast("Node builders - Missmatching variable size.");

        // This node already exist, just return it
        return node;
      } else {
        // if not found, create a new variable node
        return VariableNode::create(varName, size, *this);
      }
    }

    SharedAbstractNode Context::zx(triton::uint32 sizeExt, SharedAbstractNode expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      return ZxNode::create(sizeExt, expr);
    }

    void Context::initVariable(const std::string& name, const triton::uint512& value, SharedAbstractNode const& node) {
      // FIXME: Use insert and check result
      auto it = this->valueMapping.find(name);
      if (it == this->valueMapping.end())
        this->valueMapping.insert(std::make_pair(name, std::make_pair(node, value)));
      else
        throw triton::ast::exceptions::Ast("Ast variable already initialized");
    }

    void Context::updateVariable(const std::string& name, const triton::uint512& value) {
      auto& kv = this->valueMapping.at(name);
      kv.second = value;
      kv.first->init();
    }

    SharedAbstractNode Context::getVariableNode(const std::string& name) {
      auto it = this->valueMapping.find(name);
      if (it == this->valueMapping.end())
        return nullptr;
      else
        return it->second.first;
    }

    const triton::uint512& Context::getValueForVariable(const std::string& varName) const {
      try {
        return this->valueMapping.at(varName).second;
      } catch(const std::out_of_range&) {
        throw triton::ast::exceptions::Ast("Context::getValueForVariable(): Variable doesn't exists");
      }
    }

    void Context::setRepresentationMode(triton::uint32 mode) {
      this->astRepresentation.setMode(mode);
    }

    triton::uint32 Context::getRepresentationMode(void) const {
      return astRepresentation.getMode();
    }

    std::ostream& Context::print(std::ostream& stream, AbstractNode* node) {
      return astRepresentation.print(stream, node);
    }

  }; /* ast namespace */
}; /* triton namespace */
