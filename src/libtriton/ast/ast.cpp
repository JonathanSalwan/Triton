//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <algorithm>
#include <cmath>
#include <new>
#include <stack>
#include <unordered_map>
#include <utility>

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicVariable.hpp>



namespace triton {
  namespace ast {

    /* ====== Abstract node */

    AbstractNode::AbstractNode(triton::ast::ast_e type, AstContext& ctxt): ctxt(ctxt) {
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;
      this->type        = type;
    }


    AbstractNode::~AbstractNode() {
      /* virtual */
    }


    AstContext& AbstractNode::getContext(void) const {
      return this->ctxt;
    }


    triton::ast::ast_e AbstractNode::getType(void) const {
      return this->type;
    }


    triton::uint32 AbstractNode::getBitvectorSize(void) const {
      return this->size;
    }


    triton::uint512 AbstractNode::getBitvectorMask(void) const {
      triton::uint512 mask = -1;
      mask = mask >> (512 - this->size);
      return mask;
    }


    bool AbstractNode::isSigned(void) const {
      if ((this->eval >> (this->size-1)) & 1)
        return true;
      return false;
    }


    bool AbstractNode::isSymbolized(void) const {
      return this->symbolized;
    }


    bool AbstractNode::isLogical(void) const {
      switch (this->type) {
        case BVSGE_NODE:
        case BVSGT_NODE:
        case BVSLE_NODE:
        case BVSLT_NODE:
        case BVUGE_NODE:
        case BVUGT_NODE:
        case BVULE_NODE:
        case BVULT_NODE:
        case DISTINCT_NODE:
        case EQUAL_NODE:
        case IFF_NODE:
        case LAND_NODE:
        case LNOT_NODE:
        case LOR_NODE:
          return true;

        case REFERENCE_NODE:
          return this->logical;

        default:
          break;
      }

      return false;
    }


    bool AbstractNode::equalTo(const SharedAbstractNode& other) const {
      return (this->evaluate() == other->evaluate()) &&
             (this->getBitvectorSize() == other->getBitvectorSize()) &&
             (this->hash(1) == other->hash(1));
    }


    triton::uint512 AbstractNode::evaluate(void) const {
      return this->eval;
    }


    void AbstractNode::initParents(void) {
      for (auto& sp : this->getParents())
        sp->init();
    }


    std::vector<SharedAbstractNode>& AbstractNode::getChildren(void) {
      return this->children;
    }


    std::vector<SharedAbstractNode> AbstractNode::getParents(void) {
      std::vector<SharedAbstractNode> res;
      std::vector<AbstractNode*> toRemove;

      for (auto& kv: parents) {
        if (auto sp = kv.second.second.lock())
          res.push_back(sp);
        else
          toRemove.push_back(kv.first);
      }

      for(auto* an: toRemove)
        parents.erase(an);

      return res;
    }


    void AbstractNode::setParent(AbstractNode* p) {
      auto it = parents.find(p);

      if (it == parents.end()) {
        auto A = p->shared_from_this();
        this->parents.insert(std::make_pair(p, std::make_pair(1, WeakAbstractNode(A))));
      }
      else {
        if (it->second.second.expired()) {
          parents.erase(it);
          auto A = p->shared_from_this();
          this->parents.insert(std::make_pair(p, std::make_pair(1, WeakAbstractNode(A))));
        }
        // Ptr already in, add it for the counter
        else {
          it->second.first += 1;
        }
      }
    }


    void AbstractNode::removeParent(AbstractNode* p) {
      auto it = this->parents.find(p);

      if(it == parents.end())
        return;

      it->second.first--;
      if(it->second.first == 0)
        this->parents.erase(it);
    }


    void AbstractNode::setParent(std::set<AbstractNode*>& p) {
      for (auto ptr : p)
        this->setParent(ptr);
    }


    void AbstractNode::addChild(const SharedAbstractNode& child) {
      this->children.push_back(child);
    }


    void AbstractNode::setChild(triton::uint32 index, const SharedAbstractNode& child) {
      if (index >= this->children.size())
        throw triton::exceptions::Ast("AbstractNode::setChild(): Invalid index.");

      if (child == nullptr)
        throw triton::exceptions::Ast("AbstractNode::setChild(): child cannot be null.");

      /* Remove the parent of the old child */
      this->children[index]->removeParent(this);

      /* Setup the parent of the child */
      child->setParent(this);

      /* Setup the child of the parent */
      this->children[index] = child;
    }


    void AbstractNode::setBitvectorSize(triton::uint32 size) {
      this->size = size;
    }


    std::string AbstractNode::str(void) const {
      std::stringstream s;
      s << this;
      if (!s.str().empty())
        return s.str();
      return nullptr;
    }


    /* ====== assert */


    AssertNode::AssertNode(const SharedAbstractNode& expr): AbstractNode(ASSERT_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void AssertNode::init(void) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("AssertNode::init(): Must take at least one child.");

      if (this->children[0]->isLogical() == false)
        throw triton::exceptions::Ast("AssertNode::init(): Must take a logical node as argument.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 AssertNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvadd */


    BvaddNode::BvaddNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVADD_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvaddNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvaddNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvaddNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() + this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvaddNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvand */


    BvandNode::BvandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvandNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvandNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() & this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }



    /* ====== bvashr (shift with sign extension fill) */


    BvashrNode::BvashrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVASHR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvashrNode::init(void) {
      triton::uint32 shift  = 0;
      triton::uint512 mask  = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvashrNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvashrNode::init(): Must take two nodes of same size.");

      value = this->children[0]->evaluate();
      shift = this->children[1]->evaluate().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      /* Mask based on the sign */
      if (this->children[0]->isSigned()) {
        mask = 1;
        mask = ((mask << (this->size-1)) & this->getBitvectorMask());
      }

      if (shift >= this->size && this->children[0]->isSigned()) {
        this->eval = -1;
        this->eval &= this->getBitvectorMask();
      }

      else if (shift >= this->size && !this->children[0]->isSigned()) {
        this->eval = 0;
      }

      else if (shift == 0) {
        this->eval = value;
      }

      else {
        this->eval = value & this->getBitvectorMask();
        for (triton::uint32 index = 0; index < shift; index++) {
          this->eval = (((this->eval >> 1) | mask) & this->getBitvectorMask());
        }
      }

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvashrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvlshr (shift with zero filled) */


    BvlshrNode::BvlshrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVLSHR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvlshrNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvlshrNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvlshrNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() >> this->children[1]->evaluate().convert_to<triton::uint32>());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvlshrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvmul */


    BvmulNode::BvmulNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVMUL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvmulNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvmulNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvmulNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() * this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvmulNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnand */


    BvnandNode::BvnandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVNAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvnandNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvnandNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvnandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~(this->children[0]->evaluate() & this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvnandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvneg */


    BvnegNode::BvnegNode(const SharedAbstractNode& expr): AbstractNode(BVNEG_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void BvnegNode::init(void) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("BvnegNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((-(this->children[0]->evaluate().convert_to<triton::sint512>())).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvnegNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnor */


    BvnorNode::BvnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVNOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvnorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvnorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~(this->children[0]->evaluate() | this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnot */


    BvnotNode::BvnotNode(const SharedAbstractNode& expr): AbstractNode(BVNOT_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void BvnotNode::init(void) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("BvnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~this->children[0]->evaluate() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvor */


    BvorNode::BvorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[0]->getBitvectorSize())
        throw triton::exceptions::Ast("BvorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() | this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvrol */


    BvrolNode::BvrolNode(const SharedAbstractNode& expr, triton::uint32 rot): BvrolNode(expr, expr->getContext().integer(rot)) {
    }


    BvrolNode::BvrolNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot): AbstractNode(BVROL_NODE, expr->getContext()) {
      this->addChild(expr);
      this->addChild(rot);
    }


    void BvrolNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvrolNode::init(): Must take at least two children.");

      if (this->children[1]->getType() != INTEGER_NODE)
        throw triton::exceptions::Ast("BvrolNode::init(): rot must be a INTEGER_NODE.");

      rot   = reinterpret_cast<IntegerNode*>(this->children[1].get())->getInteger().convert_to<triton::uint32>();
      value = this->children[0]->evaluate();

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value << rot) | (value >> (this->size - rot))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvrolNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvror */


    BvrorNode::BvrorNode(const SharedAbstractNode& expr, triton::uint32 rot): BvrorNode(expr, expr->getContext().integer(rot)) {
    }


    BvrorNode::BvrorNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot): AbstractNode(BVROR_NODE, expr->getContext()) {
      this->addChild(expr);
      this->addChild(rot);
    }


    void BvrorNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvrorNode::init(): Must take at least two children.");

      if (this->children[1]->getType() != INTEGER_NODE)
        throw triton::exceptions::Ast("BvrorNode::init(): rot must be a INTEGER_NODE.");

      rot   = reinterpret_cast<IntegerNode*>(this->children[1].get())->getInteger().convert_to<triton::uint32>();
      value = this->children[0]->evaluate();

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value >> rot) | (value << (this->size - rot))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvrorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsdiv */


    BvsdivNode::BvsdivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSDIV_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsdivNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (op2Signed == 0) {
        this->eval = (op1Signed < 0 ? 1 : -1);
        this->eval &= this->getBitvectorMask();
      }
      else
        this->eval = ((op1Signed / op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsdivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsge */


    BvsgeNode::BvsgeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSGE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsgeNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed >= op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsgeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsgt */


    BvsgtNode::BvsgtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSGT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsgtNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed > op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsgtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvshl */


    BvshlNode::BvshlNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSHL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvshlNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvshlNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvshlNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() << this->children[1]->evaluate().convert_to<triton::uint32>()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvshlNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsle */


    BvsleNode::BvsleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSLE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsleNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsleNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed <= op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvslt */


    BvsltNode::BvsltNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSLT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsltNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsltNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsltNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed < op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsltNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsmod - 2's complement signed remainder (sign follows divisor) */


    BvsmodNode::BvsmodNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSMOD_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsmodNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = ((((op1Signed % op2Signed) + op2Signed) % op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsmodNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsrem - 2's complement signed remainder (sign follows dividend) */


    BvsremNode::BvsremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSREM_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsremNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsremNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = ((op1Signed - ((op1Signed / op2Signed) * op2Signed)).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsub */


    BvsubNode::BvsubNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSUB_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsubNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsubNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsubNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() - this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvsubNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvudiv */


    BvudivNode::BvudivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUDIV_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvudivNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvudivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvudivNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = (-1 & this->getBitvectorMask());
      else
        this->eval = (this->children[0]->evaluate() / this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvudivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvuge */


    BvugeNode::BvugeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUGE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvugeNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvugeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvugeNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() >= this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvugeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvugt */


    BvugtNode::BvugtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUGT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvugtNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvugtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvugtNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() > this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvugtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvule */


    BvuleNode::BvuleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVULE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvuleNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvuleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvuleNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() <= this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvuleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvult */


    BvultNode::BvultNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVULT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvultNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvultNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvultNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() < this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvultNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvurem */


    BvuremNode::BvuremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUREM_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvuremNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvuremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvuremNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = (this->children[0]->evaluate() % this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvuremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxnor */


    BvxnorNode::BvxnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVXNOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvxnorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvxnorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvxnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~(this->children[0]->evaluate() ^ this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvxnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxor */


    BvxorNode::BvxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVXOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvxorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvxorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvxorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() ^ this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvxorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bv */


    BvNode::BvNode(triton::uint512 value, triton::uint32 size, AstContext& ctxt): AbstractNode(BV_NODE, ctxt) {
      this->addChild(ctxt.integer(value));
      this->addChild(ctxt.integer(size));
    }


    void BvNode::init(void) {
      triton::uint512 value = 0;
      triton::uint32 size   = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvNode::init(): Must take at least two children.");

      if (this->children[0]->getType() != INTEGER_NODE || this->children[1]->getType() != INTEGER_NODE)
        throw triton::exceptions::Ast("BvNode::init(): Size and value must be a INTEGER_NODE.");

      value = reinterpret_cast<IntegerNode*>(this->children[0].get())->getInteger();
      size  = reinterpret_cast<IntegerNode*>(this->children[1].get())->getInteger().convert_to<triton::uint32>();

      if (!size)
        throw triton::exceptions::Ast("BvNode::init(): Size connot be equal to zero.");

      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("BvNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      /* Init attributes */
      this->size = size;
      this->eval = (value & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 BvNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== compound */


    void CompoundNode::init(void) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("CompoundNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 0;
      this->eval = 0;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 CompoundNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== concat */


    ConcatNode::ConcatNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(CONCAT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void ConcatNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("ConcatNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 0;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->size += this->children[index]->getBitvectorSize();
      }

      if (this->size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("ConcatNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = this->children[0]->evaluate();
      for (triton::uint32 index = 0; index < this->children.size()-1; index++)
        this->eval = ((this->eval << this->children[index+1]->getBitvectorSize()) | this->children[index+1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 ConcatNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Declare */


    DeclareNode::DeclareNode(const SharedAbstractNode& var): AbstractNode(DECLARE_NODE, var->getContext()) {
      this->addChild(var);
    }


    void DeclareNode::init(void) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("DeclareNode::init(): Must take at least one child.");

      if (this->children[0]->getType() != VARIABLE_NODE)
        throw triton::exceptions::Ast("DeclareNode::init(): The child node must be a VARIABLE_NODE.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = this->children[0]->evaluate();

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 DeclareNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Distinct node */


    DistinctNode::DistinctNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(DISTINCT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void DistinctNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("DistinctNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("DistinctNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() != this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 DistinctNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== equal */


    EqualNode::EqualNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(EQUAL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void EqualNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("EqualNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("EqualNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() == this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 EqualNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== extract */


    ExtractNode::ExtractNode(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr): AbstractNode(EXTRACT_NODE, expr->getContext()) {
      this->addChild(this->ctxt.integer(high));
      this->addChild(this->ctxt.integer(low));
      this->addChild(expr);
    }


    void ExtractNode::init(void) {
      triton::uint32 high = 0;
      triton::uint32 low  = 0;

      if (this->children.size() < 3)
        throw triton::exceptions::Ast("ExtractNode::init(): Must take at least three children.");

      if (this->children[0]->getType() != INTEGER_NODE || this->children[1]->getType() != INTEGER_NODE)
        throw triton::exceptions::Ast("ExtractNode::init(): The highest and lower bit must be a INTEGER_NODE.");

      high = reinterpret_cast<IntegerNode*>(this->children[0].get())->getInteger().convert_to<triton::uint32>();
      low  = reinterpret_cast<IntegerNode*>(this->children[1].get())->getInteger().convert_to<triton::uint32>();

      if (low > high)
        throw triton::exceptions::Ast("ExtractNode::init(): The high bit must be greater than the low bit.");

      /* Init attributes */
      this->size = ((high - low) + 1);
      this->eval = ((this->children[2]->evaluate() >> low) & this->getBitvectorMask());

      if (this->size > this->children[2]->getBitvectorSize() || high >= this->children[2]->getBitvectorSize())
        throw triton::exceptions::Ast("ExtractNode::init(): The size of the extraction is higher than the child expression.");

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 ExtractNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== iff */


    IffNode::IffNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(IFF_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void IffNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("IffNode::init(): Must take at least two children.");

      if (this->children[0]->isLogical() == false)
        throw triton::exceptions::Ast("IffNode::init(): Must take a logical node as first argument.");

      if (this->children[1]->isLogical() == false)
        throw triton::exceptions::Ast("IffNode::init(): Must take a logical node as second argument.");

      /* Init attributes */
      triton::uint512 P = this->children[0]->evaluate();
      triton::uint512 Q = this->children[1]->evaluate();

      this->size = 1;
      this->eval = (P && Q) || (!P && !Q);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 IffNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Integer node */


    IntegerNode::IntegerNode(triton::uint512 value, AstContext& ctxt): AbstractNode(INTEGER_NODE, ctxt) {
      this->value = value;
    }


    void IntegerNode::init(void) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;

      /* Init parents */
      this->initParents();
    }


    triton::uint512 IntegerNode::getInteger(void) {
      return this->value;
    }


    triton::uint512 IntegerNode::hash(triton::uint32 deep) const {
      triton::uint512 hash = this->type ^ this->value;
      return hash;
    }


    /* ====== ite */


    IteNode::IteNode(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr): AbstractNode(ITE_NODE, ifExpr->getContext()) {
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
    }


    void IteNode::init(void) {
      if (this->children.size() < 3)
        throw triton::exceptions::Ast("IteNode::init(): Must take at least three children.");

      if (this->children[0]->isLogical() == false)
        throw triton::exceptions::Ast("IteNode::init(): Must take a logical node as first argument.");

      if (this->children[1]->getBitvectorSize() != this->children[2]->getBitvectorSize())
        throw triton::exceptions::Ast("IteNode::init(): Must take two nodes of same size as 'then' and 'else' branches.");

      /* Init attributes */
      this->size = this->children[1]->getBitvectorSize();
      this->eval = this->children[0]->evaluate() ? this->children[1]->evaluate() : this->children[2]->evaluate();

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 IteNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Land */


    LandNode::LandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(LAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void LandNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("LandNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = 1;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = this->eval && this->children[index]->evaluate();

        if (this->children[index]->isLogical() == false)
          throw triton::exceptions::Ast("LandNode::init(): Must take logical nodes as arguments.");
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 LandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Let */


    LetNode::LetNode(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3): AbstractNode(LET_NODE, expr2->getContext()) {
      this->addChild(ctxt.string(alias));
      this->addChild(expr2);
      this->addChild(expr3);
    }


    void LetNode::init(void) {
      if (this->children.size() < 3)
        throw triton::exceptions::Ast("LetNode::init(): Must take at least three children.");

      if (this->children[0]->getType() != STRING_NODE)
        throw triton::exceptions::Ast("LetNode::init(): The alias node must be a STRING_NODE.");

      /* Init attributes */
      this->size = this->children[2]->getBitvectorSize();
      this->eval = this->children[2]->evaluate();

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 LetNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lnot */


    LnotNode::LnotNode(const SharedAbstractNode& expr): AbstractNode(LNOT_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void LnotNode::init(void) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("LnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 1;
      this->eval = !(this->children[0]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();

        if (this->children[index]->isLogical() == false)
          throw triton::exceptions::Ast("LnotNode::init(): Must take logical nodes arguments.");
      }


      /* Init parents */
      this->initParents();
    }


    triton::uint512 LnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lor */


    LorNode::LorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(LOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void LorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("LorNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = 0;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = this->eval || this->children[index]->evaluate();

        if (this->children[index]->isLogical() == false)
          throw triton::exceptions::Ast("LorNode::init(): Must take logical nodes as arguments.");
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 LorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Reference node */


    ReferenceNode::ReferenceNode(const triton::engines::symbolic::SharedSymbolicExpression& expr)
      : AbstractNode(REFERENCE_NODE, expr->getAst()->getContext())
      , expr(expr) {
    }


    void ReferenceNode::init(void) {
      /* Init attributes */
      this->eval        = this->expr->getAst()->evaluate();
      this->logical     = this->expr->getAst()->isLogical();
      this->size        = this->expr->getAst()->getBitvectorSize();
      this->symbolized  = this->expr->getAst()->isSymbolized();

      this->expr->getAst()->setParent(this);

      /* Init parents */
      this->initParents();
    }


    triton::uint512 ReferenceNode::hash(triton::uint32 deep) const {
      triton::uint512 hash = this->type ^ this->expr->getId();
      return hash;
    }


    const triton::engines::symbolic::SharedSymbolicExpression& ReferenceNode::getSymbolicExpression(void) const {
      return this->expr;
    }


    /* ====== String node */


    StringNode::StringNode(std::string value, AstContext& ctxt): AbstractNode(STRING_NODE, ctxt) {
      this->value = value;
    }


    void StringNode::init(void) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;

      /* Init parents */
      this->initParents();
    }


    std::string StringNode::getString(void) {
      return this->value;
    }


    triton::uint512 StringNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type;
      triton::uint32 index = 1;
      for (std::string::const_iterator it=this->value.cbegin(); it != this->value.cend(); it++)
        h = h ^ triton::ast::hash2n(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== sx */


    SxNode::SxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr): AbstractNode(SX_NODE, expr->getContext()) {
      this->addChild(ctxt.integer(sizeExt));
      this->addChild(expr);
    }


    void SxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("SxNode::init(): Must take at least two children.");

      if (this->children[0]->getType() != INTEGER_NODE)
        throw triton::exceptions::Ast("SxNode::init(): The sizeExt must be a INTEGER_NODE.");

      sizeExt = reinterpret_cast<IntegerNode*>(this->children[0].get())->getInteger().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->children[1]->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("SxNode::SxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = ((((this->children[1]->evaluate() >> (this->children[1]->getBitvectorSize()-1)) == 0) ? this->children[1]->evaluate() : (this->children[1]->evaluate() | ~(this->children[1]->getBitvectorMask()))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 SxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Variable node */


    // WARNING: A variable ast node should not live once the SymbolicVariable is dead
    VariableNode::VariableNode(const triton::engines::symbolic::SharedSymbolicVariable& symVar, AstContext& ctxt)
      : AbstractNode(VARIABLE_NODE, ctxt),
        symVar(symVar) {
    }


    void VariableNode::init(void) {
      this->size        = this->symVar->getSize();
      this->eval        = ctxt.getVariableValue(this->symVar->getName()) & this->getBitvectorMask();
      this->symbolized  = true;

      /* Init parents */
      this->initParents();
    }


    const triton::engines::symbolic::SharedSymbolicVariable& VariableNode::getSymbolicVariable() {
      return this->symVar;
    }


    triton::uint512 VariableNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type;
      triton::uint32 index = 1;

      for (char c : this->symVar->getName())
        h = h ^ triton::ast::hash2n(c, index++);

      return triton::ast::rotl(h, deep);
    }


    /* ====== zx */


    ZxNode::ZxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr): AbstractNode(ZX_NODE, expr->getContext()) {
      this->addChild(ctxt.integer(sizeExt));
      this->addChild(expr);
    }


    void ZxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("ZxNode::init(): Must take at least two children.");

      if (this->children[0]->getType() != INTEGER_NODE)
        throw triton::exceptions::Ast("ZxNode::init(): The sizeExt must be a INTEGER_NODE.");

      sizeExt = reinterpret_cast<IntegerNode*>(this->children[0].get())->getInteger().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->children[1]->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("ZxNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = (this->children[1]->evaluate() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      this->initParents();
    }


    triton::uint512 ZxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->type, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::hash2n(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }

  }; /* ast namespace */
}; /* triton namespace */



/* ====== Force templates declarations */

namespace triton {
  namespace ast {

    template TRITON_EXPORT CompoundNode::CompoundNode(const std::list<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT CompoundNode::CompoundNode(const std::vector<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT ConcatNode::ConcatNode(const std::list<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT ConcatNode::ConcatNode(const std::vector<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT LandNode::LandNode(const std::list<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT LandNode::LandNode(const std::vector<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT LorNode::LorNode(const std::list<SharedAbstractNode>& exprs, AstContext& ctxt);
    template TRITON_EXPORT LorNode::LorNode(const std::vector<SharedAbstractNode>& exprs, AstContext& ctxt);

  }; /* ast namespace */
}; /* triton namespace */



/* ====== Operators */

namespace triton {
  namespace ast {

    /* Representation dispatcher from an abstract node */
    std::ostream& operator<<(std::ostream& stream, AbstractNode* node) {
      return node->getContext().print(stream, node);
    }

  }; /* ast namespace */
}; /* triton namespace */



/* ====== Math utils */

namespace triton {
  namespace ast {

    triton::uint512 hash2n(triton::uint512 hash, triton::uint32 n) {
      triton::uint512 mask = -1;
      for (triton::uint32 i = 0; i < n; i++)
        hash = ((hash * hash) & mask);
      return hash;
    }


    triton::uint512 rotl(triton::uint512 value, triton::uint32 shift) {
      if ((shift &= 511) == 0)
        return value;
      return ((value << shift) | (value >> (512 - shift)));
    }


    triton::sint512 modularSignExtend(AbstractNode* node) {
      triton::sint512 value = 0;

      if ((node->evaluate() >> (node->getBitvectorSize()-1)) & 1) {
        value = -1;
        value = ((value << node->getBitvectorSize()) | node->evaluate());
      }
      else {
        value = node->evaluate();
      }

      return value;
    }

  }; /* ast namespace */
}; /* triton namespace */



/* ====== Node utilities */

namespace triton {
  namespace ast {

    SharedAbstractNode newInstance(AbstractNode* node, bool unroll) {
      SharedAbstractNode newNode = nullptr;

      if (node == nullptr)
        return nullptr;

      switch (node->getType()) {
        case ASSERT_NODE:               newNode = std::make_shared<AssertNode>(*reinterpret_cast<AssertNode*>(node));     break;
        case BVADD_NODE:                newNode = std::make_shared<BvaddNode>(*reinterpret_cast<BvaddNode*>(node));       break;
        case BVAND_NODE:                newNode = std::make_shared<BvandNode>(*reinterpret_cast<BvandNode*>(node));       break;
        case BVASHR_NODE:               newNode = std::make_shared<BvashrNode>(*reinterpret_cast<BvashrNode*>(node));     break;
        case BVLSHR_NODE:               newNode = std::make_shared<BvlshrNode>(*reinterpret_cast<BvlshrNode*>(node));     break;
        case BVMUL_NODE:                newNode = std::make_shared<BvmulNode>(*reinterpret_cast<BvmulNode*>(node));       break;
        case BVNAND_NODE:               newNode = std::make_shared<BvnandNode>(*reinterpret_cast<BvnandNode*>(node));     break;
        case BVNEG_NODE:                newNode = std::make_shared<BvnegNode>(*reinterpret_cast<BvnegNode*>(node));       break;
        case BVNOR_NODE:                newNode = std::make_shared<BvnorNode>(*reinterpret_cast<BvnorNode*>(node));       break;
        case BVNOT_NODE:                newNode = std::make_shared<BvnotNode>(*reinterpret_cast<BvnotNode*>(node));       break;
        case BVOR_NODE:                 newNode = std::make_shared<BvorNode>(*reinterpret_cast<BvorNode*>(node));         break;
        case BVROL_NODE:                newNode = std::make_shared<BvrolNode>(*reinterpret_cast<BvrolNode*>(node));       break;
        case BVROR_NODE:                newNode = std::make_shared<BvrorNode>(*reinterpret_cast<BvrorNode*>(node));       break;
        case BVSDIV_NODE:               newNode = std::make_shared<BvsdivNode>(*reinterpret_cast<BvsdivNode*>(node));     break;
        case BVSGE_NODE:                newNode = std::make_shared<BvsgeNode>(*reinterpret_cast<BvsgeNode*>(node));       break;
        case BVSGT_NODE:                newNode = std::make_shared<BvsgtNode>(*reinterpret_cast<BvsgtNode*>(node));       break;
        case BVSHL_NODE:                newNode = std::make_shared<BvshlNode>(*reinterpret_cast<BvshlNode*>(node));       break;
        case BVSLE_NODE:                newNode = std::make_shared<BvsleNode>(*reinterpret_cast<BvsleNode*>(node));       break;
        case BVSLT_NODE:                newNode = std::make_shared<BvsltNode>(*reinterpret_cast<BvsltNode*>(node));       break;
        case BVSMOD_NODE:               newNode = std::make_shared<BvsmodNode>(*reinterpret_cast<BvsmodNode*>(node));     break;
        case BVSREM_NODE:               newNode = std::make_shared<BvsremNode>(*reinterpret_cast<BvsremNode*>(node));     break;
        case BVSUB_NODE:                newNode = std::make_shared<BvsubNode>(*reinterpret_cast<BvsubNode*>(node));       break;
        case BVUDIV_NODE:               newNode = std::make_shared<BvudivNode>(*reinterpret_cast<BvudivNode*>(node));     break;
        case BVUGE_NODE:                newNode = std::make_shared<BvugeNode>(*reinterpret_cast<BvugeNode*>(node));       break;
        case BVUGT_NODE:                newNode = std::make_shared<BvugtNode>(*reinterpret_cast<BvugtNode*>(node));       break;
        case BVULE_NODE:                newNode = std::make_shared<BvuleNode>(*reinterpret_cast<BvuleNode*>(node));       break;
        case BVULT_NODE:                newNode = std::make_shared<BvultNode>(*reinterpret_cast<BvultNode*>(node));       break;
        case BVUREM_NODE:               newNode = std::make_shared<BvuremNode>(*reinterpret_cast<BvuremNode*>(node));     break;
        case BVXNOR_NODE:               newNode = std::make_shared<BvxnorNode>(*reinterpret_cast<BvxnorNode*>(node));     break;
        case BVXOR_NODE:                newNode = std::make_shared<BvxorNode>(*reinterpret_cast<BvxorNode*>(node));       break;
        case BV_NODE:                   newNode = std::make_shared<BvNode>(*reinterpret_cast<BvNode*>(node));             break;
        case COMPOUND_NODE:             newNode = std::make_shared<CompoundNode>(*reinterpret_cast<CompoundNode*>(node)); break;
        case CONCAT_NODE:               newNode = std::make_shared<ConcatNode>(*reinterpret_cast<ConcatNode*>(node));     break;
        case DECLARE_NODE:              newNode = std::make_shared<DeclareNode>(*reinterpret_cast<DeclareNode*>(node));   break;
        case DISTINCT_NODE:             newNode = std::make_shared<DistinctNode>(*reinterpret_cast<DistinctNode*>(node)); break;
        case EQUAL_NODE:                newNode = std::make_shared<EqualNode>(*reinterpret_cast<EqualNode*>(node));       break;
        case EXTRACT_NODE:              newNode = std::make_shared<ExtractNode>(*reinterpret_cast<ExtractNode*>(node));   break;
        case IFF_NODE:                  newNode = std::make_shared<IffNode>(*reinterpret_cast<IffNode*>(node));           break;
        case INTEGER_NODE:              newNode = std::make_shared<IntegerNode>(*reinterpret_cast<IntegerNode*>(node));   break;
        case ITE_NODE:                  newNode = std::make_shared<IteNode>(*reinterpret_cast<IteNode*>(node));           break;
        case LAND_NODE:                 newNode = std::make_shared<LandNode>(*reinterpret_cast<LandNode*>(node));         break;
        case LET_NODE:                  newNode = std::make_shared<LetNode>(*reinterpret_cast<LetNode*>(node));           break;
        case LNOT_NODE:                 newNode = std::make_shared<LnotNode>(*reinterpret_cast<LnotNode*>(node));         break;
        case LOR_NODE:                  newNode = std::make_shared<LorNode>(*reinterpret_cast<LorNode*>(node));           break;
        case REFERENCE_NODE: {
          if (unroll)
            return triton::ast::newInstance(reinterpret_cast<ReferenceNode*>(node)->getSymbolicExpression()->getAst().get(), unroll);
          else
            newNode = std::make_shared<ReferenceNode>(*reinterpret_cast<ReferenceNode*>(node));
          break;
        }
        case STRING_NODE:               newNode = std::make_shared<StringNode>(*reinterpret_cast<StringNode*>(node));     break;
        case SX_NODE:                   newNode = std::make_shared<SxNode>(*reinterpret_cast<SxNode*>(node));             break;
        case VARIABLE_NODE:             newNode = std::make_shared<VariableNode>(*reinterpret_cast<VariableNode*>(node)); break;
        case ZX_NODE:                   newNode = std::make_shared<ZxNode>(*reinterpret_cast<ZxNode*>(node));             break;
        default:
          throw triton::exceptions::Ast("triton::ast::newInstance(): Invalid type node.");
      }

      if (newNode == nullptr)
        throw triton::exceptions::Ast("triton::ast::newInstance(): No enough memory.");

      /* Remove parents as this is a new node which has no connections with original AST */
      newNode->getParents().clear();

      /* Create new instances of children and set their new parents */
      auto& children = newNode->getChildren();
      for (triton::usize idx = 0; idx < children.size(); idx++) {
        children[idx] = triton::ast::newInstance(children[idx].get(), unroll);
        children[idx]->setParent(newNode.get());
      }

      return newNode;
    }


    SharedAbstractNode unrollAst(const triton::ast::SharedAbstractNode& node) {
      return triton::ast::newInstance(node.get(), true);
    }


    void nodesExtraction(std::deque<SharedAbstractNode>* output, const SharedAbstractNode& node, bool unroll, bool revert) {
      std::unordered_map<triton::usize, std::set<SharedAbstractNode>> sortedlist;
      std::deque<std::pair<SharedAbstractNode,triton::usize>> worklist;
      triton::usize depth = 0;

      if (node == nullptr)
        throw triton::exceptions::Ast("triton::ast::nodesExtraction(): Node cannot be null.");

      /*
       *  We use a worklist strategy to avoid recursive calls
       *  and so stack overflow when going through a big AST.
       */
      worklist.push_back({node, 0});
      while (worklist.empty() == false) {
        auto ast = worklist.front().first;
        auto lvl = worklist.front().second;
        worklist.pop_front();

        /* Keep up-to-date the depth of the tree */
        depth = std::max(depth, lvl);

        /* Proceed children */
        for (const auto& child : ast->getChildren()) {
          if (std::find(worklist.begin(), worklist.end(), std::make_pair(child, lvl + 1)) == worklist.end()) {
            worklist.push_back({child, lvl + 1});
          }
        }

        /* If unroll is true, we unroll all references */
        if (unroll == true && ast->getType() == REFERENCE_NODE) {
          const auto& ref = reinterpret_cast<ReferenceNode*>(ast.get())->getSymbolicExpression()->getAst();
          if (std::find(worklist.begin(), worklist.end(), std::make_pair(ref, lvl + 1)) == worklist.end()) {
            worklist.push_back({ref, lvl + 1});
          }
        }

        sortedlist[lvl].insert(ast);
      }

      /* Sort nodes into the output list */
      for (triton::usize index = 0; index <= depth; index++) {
        auto& nodes = revert ? sortedlist[depth - index] : sortedlist[index];
        for (auto&& n : nodes) {
          if (std::find(output->begin(), output->end(), n) == output->end()) {
            output->push_back(n);
          }
        }
      }
    }


    std::deque<SharedAbstractNode> lookingForNodes(const SharedAbstractNode& node, triton::ast::ast_e match) {
      std::stack<triton::ast::AbstractNode*>      worklist;
      std::deque<triton::ast::SharedAbstractNode> result;
      std::set<const triton::ast::AbstractNode*>  visited;

      worklist.push(node.get());
      while (!worklist.empty()) {
        auto current = worklist.top();
        worklist.pop();

        // This means that node is already in work_stack and we will not need to convert it second time
        if (visited.find(current) != visited.end()) {
          continue;
        }

        visited.insert(current);
        if (match == triton::ast::ANY_NODE || current->getType() == match)
          result.push_front(current->shared_from_this());

        if (current->getType() == REFERENCE_NODE) {
          worklist.push(reinterpret_cast<triton::ast::ReferenceNode *>(current)->getSymbolicExpression()->getAst().get());
        } else {
          for (const auto &child : current->getChildren())
            worklist.push(child.get());
        }
      }

      return result;
    }

  }; /* ast namespace */
}; /* triton namespace */
