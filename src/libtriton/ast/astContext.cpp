//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>



namespace triton {
  namespace ast {

    AstContext::AstContext() {
    }


    AstContext::AstContext(const AstContext& other)
      : astRepresentation(other.astRepresentation),
        valueMapping(other.valueMapping) {
    }


    AstContext::~AstContext() {
      this->valueMapping.clear();
    }


    AstContext& AstContext::operator=(const AstContext& other) {
      this->astRepresentation = other.astRepresentation;
      this->valueMapping = other.valueMapping;
      return *this;
    }


    SharedAbstractNode AstContext::assert_(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<AssertNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bv(triton::uint512 value, triton::uint32 size) {
      SharedAbstractNode node = std::make_shared<BvNode>(value, size, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvadd(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvaddNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvandNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvashr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvashrNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvfalse(void) {
      SharedAbstractNode node = std::make_shared<BvNode>(0, 1, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvlshr(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvlshrNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvmul(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvmulNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvnand(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvnandNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvneg(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvnegNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvnorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvnot(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvnotNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvrol(triton::uint32 rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvrolNode>(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvrol(const SharedAbstractNode& rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvrolNode>(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvror(triton::uint32 rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvrorNode>(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvror(const SharedAbstractNode& rot, const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<BvrorNode>(rot, expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsdiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsdivNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsgeNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsgt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsgtNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvshl(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvshlNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsle(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsleNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvslt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsltNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsmod(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsmodNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsrem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsremNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvsub(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvsubNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvtrue(void) {
      SharedAbstractNode node = std::make_shared<BvNode>(1, 1, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvudiv(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvudivNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvuge(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvugeNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvugt(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvugtNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvule(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvuleNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvult(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvultNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvurem(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvuremNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


     SharedAbstractNode AstContext::bvxnor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvxnorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::bvxor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<BvxorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::compound(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::compound(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::concat(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<ConcatNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::concat(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::concat(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::decimal(triton::uint512 value) {
      SharedAbstractNode node = std::make_shared<DecimalNode>(value, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::declare(const SharedAbstractNode& var) {
      SharedAbstractNode node = std::make_shared<DeclareNode>(var);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::distinct(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<DistinctNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::equal(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<EqualNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::extract(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr) {
      /* Optimization: If we extract the full size of expr, just return expr */
      if (low == 0 && (high + 1) == expr->getBitvectorSize())
        return expr;

      SharedAbstractNode node = std::make_shared<ExtractNode>(high, low, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      node->init();
      return node;
    }


    SharedAbstractNode AstContext::ite(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr) {
      SharedAbstractNode node = std::make_shared<IteNode>(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::land(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<LandNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::land(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::land(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::let(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3) {
      SharedAbstractNode node = std::make_shared<LetNode>(alias, expr2, expr3);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::lnot(const SharedAbstractNode& expr) {
      SharedAbstractNode node = std::make_shared<LnotNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::lor(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) {
      SharedAbstractNode node = std::make_shared<LorNode>(expr1, expr2);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    template TRITON_EXPORT SharedAbstractNode AstContext::lor(const std::vector<SharedAbstractNode>& exprs);
    template TRITON_EXPORT SharedAbstractNode AstContext::lor(const std::list<SharedAbstractNode>& exprs);


    SharedAbstractNode AstContext::reference(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
      SharedAbstractNode node = std::make_shared<ReferenceNode>(expr);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::string(std::string value) {
      SharedAbstractNode node = std::make_shared<StringNode>(value, *this);
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
      node->init();
      return node;
    }


    SharedAbstractNode AstContext::sx(triton::uint32 sizeExt, const SharedAbstractNode& expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      SharedAbstractNode node = std::make_shared<SxNode>(sizeExt, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      node->init();
      return node;
    }


    SharedAbstractNode AstContext::variable(const triton::engines::symbolic::SharedSymbolicVariable& symVar) {
      // try to get node from variable pool
      auto it = this->valueMapping.find(symVar->getName());
      if (it != this->valueMapping.end()) {
        auto& node = it->second.first;

        if (node->getBitvectorSize() != symVar->getSize())
          throw triton::exceptions::Ast("Node builders - Missmatching variable size.");

        // This node already exist, just return it
        node->init();
        return node;
      }
      else {
        // if not found, create a new variable node
        SharedAbstractNode node = std::make_shared<VariableNode>(symVar, *this);
        this->initVariable(symVar->getName(), 0, node);
        if (node == nullptr)
          throw triton::exceptions::Ast("Node builders - Not enough memory");
        node->init();
        return node;
      }
    }


    SharedAbstractNode AstContext::zx(triton::uint32 sizeExt, const SharedAbstractNode& expr) {
      /* Optimization: Just return expr if the extend is zero */
      if (sizeExt == 0)
        return expr;

      SharedAbstractNode node = std::make_shared<ZxNode>(sizeExt, expr);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      node->init();
      return node;
    }


    SharedAbstractNode AstContext::array(triton::uint32 addrSize) {
      SharedAbstractNode node = std::make_shared<ArrayNode>(addrSize, *this);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      node->init();
      return node;
    }


    SharedAbstractNode AstContext::select(const SharedAbstractNode& a, const SharedAbstractNode& i) {
      SharedAbstractNode node = std::make_shared<SelectNode>(a, i);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      node->init();
      return node;
    }


    SharedAbstractNode AstContext::store(const SharedAbstractNode& a, const SharedAbstractNode& i, const SharedAbstractNode& v) {
      SharedAbstractNode node = std::make_shared<StoreNode>(a, i, v);

      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");

      node->init();
      return node;
    }


    void AstContext::initVariable(const std::string& name, const triton::uint512& value, const SharedAbstractNode& node) {
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
