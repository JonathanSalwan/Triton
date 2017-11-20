//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <tritonast/nodes.hpp>
#include <tritonast/context.hpp>
#include <tritonast/exceptions.hpp>
#include <tritonast/representations/representation.hpp>
#include <tritonast/solvers/z3/tritonToZ3Ast.hpp>

#include <cmath>
#include <new>


namespace triton {
  namespace ast {

    /* ====== Abstract node */

    AbstractNode::AbstractNode(enum kind_e kind, Context& ctxt): ctxt(ctxt) {
      this->eval        = 0;
      this->kind        = kind;
      this->size        = 0;
      this->symbolized  = false;
    }

    AbstractNode::AbstractNode(const AbstractNode& copy, Context& ctxt): ctxt(ctxt) {
      this->eval        = copy.eval;
      this->kind        = copy.kind;
      this->parents     = copy.parents;
      this->size        = copy.size;
      this->symbolized  = copy.symbolized;

      for (triton::uint32 index = 0; index < copy.children.size(); index++)
        this->children.push_back(triton::ast::newInstance(copy.children[index].get()));
    }


    AbstractNode::~AbstractNode() {
      /* virtual */
    }


    Context& AbstractNode::getContext(void) const {
      return this->ctxt;
    }


    enum kind_e AbstractNode::getKind(void) const {
      return this->kind;
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
      switch (this->kind) {
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
        case LAND_NODE:
        case LNOT_NODE:
        case LOR_NODE:
          return true;

        default:
          break;
      }

      return false;
    }


    bool AbstractNode::equalTo(const AbstractNode& other) const {
      return (this->evaluate() == other.evaluate()) &&
             (this->getBitvectorSize() == other.getBitvectorSize()) &&
             (this->hash(1) == other.hash(1));
    }


    bool AbstractNode::equalTo(AbstractNode* other) const {
      return this->equalTo(*other);
    }


    triton::uint512 AbstractNode::evaluate(void) const {
      return this->eval;
    }

    void AbstractNode::updateParents() {
      for(auto& sp: getParents())
        sp->init();
    }


    std::vector<SharedAbstractNode>& AbstractNode::getChildren(void) {
      return this->children;
    }


    std::vector<SharedAbstractNode> AbstractNode::getParents(void) {
      std::vector<SharedAbstractNode> res;
      std::vector<AbstractNode*> toRemove;
      for(auto& kv: parents) {
        if(auto sp = kv.second.lock())
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
      if(it == parents.end()) {
        auto A = p->shared_from_this();
        this->parents.insert(std::make_pair(p, std::weak_ptr<AbstractNode>(A)));
      }  else {
        if(it->second.expired()) {
          parents.erase(it);
          auto A = p->shared_from_this();
          this->parents.insert(std::make_pair(p, std::weak_ptr<AbstractNode>(A)));
        }
        else
        {}; // Ptr already in
      }
    }


    void AbstractNode::removeParent(AbstractNode* p) {
      this->parents.erase(parents.find(p));
    }


    void AbstractNode::setParent(std::vector<AbstractNode*>& p) {
      for (auto ptr: p)
        this->setParent(ptr);
    }


    void AbstractNode::addChild(SharedAbstractNode const& child) {
      child->setParent(this);
      this->children.push_back(child);
    }


    void AbstractNode::setChild(triton::uint32 index, SharedAbstractNode const& child) {
      if (index >= this->children.size())
        throw triton::ast::exceptions::Ast("AbstractNode::setChild(): Invalid index.");

      if (child == nullptr)
        throw triton::ast::exceptions::Ast("AbstractNode::setChild(): child cannot be null.");

      /* Setup the parent of the child */
      child->setParent(this);

      /* Remove the parent of the old child */
      this->children[index]->removeParent(this);

      /* Setup the child of the parent */
      this->children[index] = child;
    }


    void AbstractNode::setBitvectorSize(triton::uint32 size) {
      this->size = size;
    }


    /* ====== bvadd */


    BvaddNode::BvaddNode(Context& ctxt):
      AbstractNode(BVADD_NODE, ctxt)
    {}


    SharedAbstractNode BvaddNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvaddNode>(new BvaddNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvaddNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvaddNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvaddNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() + this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvaddNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvand */


    BvandNode::BvandNode(Context& ctxt):
      AbstractNode(BVAND_NODE, ctxt)
    {
    }

    std::shared_ptr<BvandNode> BvandNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2)
    {
      auto node = std::shared_ptr<BvandNode>(new BvandNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvandNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvandNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() & this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }



    /* ====== bvashr (shift with sign extension fill) */


    BvashrNode::BvashrNode(Context& ctxt):
        AbstractNode(BVASHR_NODE, ctxt)
    {}



    SharedAbstractNode BvashrNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvashrNode>(new BvashrNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvashrNode::init(void) {
      triton::uint32 shift  = 0;
      triton::uint512 mask  = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvashrNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvashrNode::init(): Must take two nodes of same size.");

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
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvashrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvlshr (shift with zero filled) */


    BvlshrNode::BvlshrNode(Context& ctxt):
      AbstractNode(BVLSHR_NODE, ctxt)
    {}



    SharedAbstractNode BvlshrNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvlshrNode>(new BvlshrNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvlshrNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvlshrNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvlshrNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() >> this->children[1]->evaluate().convert_to<triton::uint32>());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvlshrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvmul */


    BvmulNode::BvmulNode(Context& ctxt):
        AbstractNode(BVMUL_NODE, ctxt)
    {}



    SharedAbstractNode BvmulNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvmulNode>(new BvmulNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvmulNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvmulNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvmulNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() * this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvmulNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnand */


    BvnandNode::BvnandNode(Context& ctxt):
        AbstractNode(BVNAND_NODE,ctxt)
    {}



    SharedAbstractNode BvnandNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvnandNode>(new BvnandNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvnandNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvnandNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvnandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~(this->children[0]->evaluate() & this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvnandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvneg */


    BvnegNode::BvnegNode(Context& ctxt):
        AbstractNode(BVNEG_NODE, ctxt)

    {}



    SharedAbstractNode BvnegNode::create(SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<BvnegNode>(new BvnegNode(expr->getContext()));
      node->addChild(expr);
      node->init();
      return node;
    }


    void BvnegNode::init(void) {
      if (this->children.size() < 1)
        throw triton::ast::exceptions::Ast("BvnegNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((-(this->children[0]->evaluate().convert_to<triton::sint512>())).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvnegNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnor */


    BvnorNode::BvnorNode(Context& ctxt):
      AbstractNode(BVNOR_NODE, ctxt)
    {}



    SharedAbstractNode BvnorNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvnorNode>(new BvnorNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvnorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvnorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~(this->children[0]->evaluate() | this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnot */


    BvnotNode::BvnotNode(Context& ctxt):
      AbstractNode(BVNOT_NODE, ctxt)
    {}



    SharedAbstractNode BvnotNode::create(SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<BvnotNode>(new BvnotNode(expr->getContext()));
      node->addChild(expr);
      node->init();
      return node;
    }


    void BvnotNode::init(void) {
      if (this->children.size() < 1)
        throw triton::ast::exceptions::Ast("BvnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~this->children[0]->evaluate() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvor */


    BvorNode::BvorNode(Context& ctxt):
      AbstractNode(BVOR_NODE, ctxt)
    {}



    SharedAbstractNode BvorNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvorNode>(new BvorNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[0]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() | this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvrol */


    BvrolNode::BvrolNode(Context& ctxt):
      AbstractNode(BVROL_NODE, ctxt)
    {}


    SharedAbstractNode BvrolNode::create(triton::uint32 rot, SharedAbstractNode const& expr) {
      return BvrolNode::create(expr->getContext().decimal(rot), expr);
    }


    SharedAbstractNode BvrolNode::create(SharedAbstractNode const& rot, SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<BvrolNode>(new BvrolNode(rot->getContext()));
      node->addChild(rot);
      node->addChild(expr);
      node->init();
      return node;
    }


    void BvrolNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvrolNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::ast::exceptions::Ast("BvrolNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->children[0].get())->getValue().convert_to<triton::uint32>();
      value = this->children[1]->evaluate();

      /* Init attributes */
      this->size = this->children[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value << rot) | (value >> (this->size - rot))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvrolNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvror */


    BvrorNode::BvrorNode(Context& ctxt):
      AbstractNode(BVROR_NODE, ctxt)
    {
    }


    SharedAbstractNode BvrorNode::create(triton::uint32 rot, SharedAbstractNode const& expr) {
      return BvrorNode::create(expr->getContext().decimal(rot), expr);
    }

    SharedAbstractNode BvrorNode::create(SharedAbstractNode const& rot, SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<BvrorNode>(new BvrorNode(rot->getContext()));
      node->addChild(rot);
      node->addChild(expr);
      node->init();
      return node;
    }


    void BvrorNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvrorNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::ast::exceptions::Ast("BvrorNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->children[0].get())->getValue().convert_to<triton::uint32>();
      value = this->children[1]->evaluate();

      /* Init attributes */
      this->size = this->children[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value >> rot) | (value << (this->size - rot))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvrorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsdiv */


    BvsdivNode::BvsdivNode(Context& ctxt):
      AbstractNode(BVSDIV_NODE, ctxt)
    {}



    SharedAbstractNode BvsdivNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsdivNode>(new BvsdivNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsdivNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsdivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsdivNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

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
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsdivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsge */


    BvsgeNode::BvsgeNode(Context& ctxt):
      AbstractNode(BVSGE_NODE, ctxt)
    {}



    SharedAbstractNode BvsgeNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsgeNode>(new BvsgeNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsgeNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsgeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsgeNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed >= op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsgeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsgt */


    BvsgtNode::BvsgtNode(Context& ctxt):
      AbstractNode(BVSGT_NODE, ctxt)
    {}



    SharedAbstractNode BvsgtNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsgtNode>(new BvsgtNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsgtNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsgtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsgtNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed > op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsgtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvshl */


    BvshlNode::BvshlNode(Context& ctxt): AbstractNode(BVSHL_NODE, ctxt)
    {}



    SharedAbstractNode BvshlNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvshlNode>(new BvshlNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvshlNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvshlNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvshlNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() << this->children[1]->evaluate().convert_to<triton::uint32>()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvshlNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsle */


    BvsleNode::BvsleNode(Context& ctxt):
      AbstractNode(BVSLE_NODE, ctxt)
    {}



    SharedAbstractNode BvsleNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsleNode>(new BvsleNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }

    void BvsleNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsleNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed <= op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvslt */


    BvsltNode::BvsltNode(Context& ctxt):
      AbstractNode(BVSLT_NODE, ctxt)
    {}



    SharedAbstractNode BvsltNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsltNode>(new BvsltNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsltNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsltNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsltNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed < op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsltNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsmod - 2's complement signed remainder (sign follows divisor) */


    BvsmodNode::BvsmodNode(Context& ctxt):
      AbstractNode(BVSMOD_NODE, ctxt)
    {}



    SharedAbstractNode BvsmodNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsmodNode>(new BvsmodNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsmodNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsmodNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsmodNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = ((((op1Signed % op2Signed) + op2Signed) % op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsmodNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsrem - 2's complement signed remainder (sign follows dividend) */


    BvsremNode::BvsremNode(Context& ctxt): AbstractNode(BVSREM_NODE, ctxt)
    {}



    SharedAbstractNode BvsremNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsremNode>(new BvsremNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsremNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsremNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      triton::sint512 op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      triton::sint512 op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = ((op1Signed - ((op1Signed / op2Signed) * op2Signed)).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsub */


    BvsubNode::BvsubNode(Context& ctxt):
      AbstractNode(BVSUB_NODE, ctxt)
    {}



    SharedAbstractNode BvsubNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvsubNode>(new BvsubNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvsubNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvsubNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvsubNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = ((this->children[0]->evaluate() - this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvsubNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvudiv */


    BvudivNode::BvudivNode(Context& ctxt):
      AbstractNode(BVUDIV_NODE, ctxt)
    {}



    SharedAbstractNode BvudivNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvudivNode>(new BvudivNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvudivNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvudivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvudivNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = (-1 & this->getBitvectorMask());
      else
        this->eval = (this->children[0]->evaluate() / this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvudivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvuge */


    BvugeNode::BvugeNode(Context& ctxt):
      AbstractNode(BVUGE_NODE, ctxt)
    {}



    SharedAbstractNode BvugeNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvugeNode>(new BvugeNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvugeNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvugeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvugeNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() >= this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvugeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvugt */


    BvugtNode::BvugtNode(Context& ctxt):
      AbstractNode(BVUGT_NODE, ctxt)
    {}



    SharedAbstractNode BvugtNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvugtNode>(new BvugtNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvugtNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvugtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvugtNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() > this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvugtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvule */


    BvuleNode::BvuleNode(Context& ctxt):
      AbstractNode(BVULE_NODE, ctxt)
    {}



    SharedAbstractNode BvuleNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvuleNode>(new BvuleNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvuleNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvuleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvuleNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() <= this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvuleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvult */


    BvultNode::BvultNode(Context& ctxt):
      AbstractNode(BVULT_NODE, ctxt)
    {}



    SharedAbstractNode BvultNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvultNode>(new BvultNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvultNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvultNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvultNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() < this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvultNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvurem */


    BvuremNode::BvuremNode(Context& ctxt):
      AbstractNode(BVUREM_NODE, ctxt)
    {}



    SharedAbstractNode BvuremNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvuremNode>(new BvuremNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvuremNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvuremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvuremNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = (this->children[0]->evaluate() % this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvuremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxnor */


    BvxnorNode::BvxnorNode(Context& ctxt):
      AbstractNode(BVXNOR_NODE, ctxt)
    {}



    SharedAbstractNode BvxnorNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvxnorNode>(new BvxnorNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvxnorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvxnorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvxnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (~(this->children[0]->evaluate() ^ this->children[1]->evaluate()) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvxnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxor */


    BvxorNode::BvxorNode(Context& ctxt):
      AbstractNode(BVXOR_NODE, ctxt)
    {}



    SharedAbstractNode BvxorNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<BvxorNode>(new BvxorNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void BvxorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvxorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("BvxorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->children[0]->getBitvectorSize();
      this->eval = (this->children[0]->evaluate() ^ this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvxorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bv */


    BvNode::BvNode(Context& ctxt):
      AbstractNode(BV_NODE, ctxt)
    {}



    SharedAbstractNode BvNode::create(triton::uint512 value, triton::uint32 size, Context& ctxt) {
      auto node = std::shared_ptr<BvNode>(new BvNode(ctxt));
      node->addChild(ctxt.decimal(value));
      node->addChild(ctxt.decimal(size));
      node->init();
      return node;
    }


    void BvNode::init(void) {
      triton::uint512 value = 0;
      triton::uint32 size   = 0;

      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("BvNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE || this->children[1]->getKind() != DECIMAL_NODE)
        throw triton::ast::exceptions::Ast("BvNode::init(): Size and value must be a DECIMAL_NODE.");

      value = reinterpret_cast<DecimalNode*>(this->children[0].get())->getValue();
      size  = reinterpret_cast<DecimalNode*>(this->children[1].get())->getValue().convert_to<triton::uint32>();

      if (!size)
        throw triton::ast::exceptions::Ast("BvNode::init(): Size connot be equal to zero.");

      if (size > triton::max_bits_supported)
        throw triton::ast::exceptions::Ast("BvNode::init(): Size connot be greater than " + std::to_string(triton::max_bits_supported) + ".");

      /* Init attributes */
      this->size = size;
      this->eval = (value & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 BvNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== concat */


    ConcatNode::ConcatNode(Context& ctxt):
      AbstractNode(CONCAT_NODE, ctxt)
    {}



    SharedAbstractNode ConcatNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<ConcatNode>(new ConcatNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }

    template SharedAbstractNode ConcatNode::create(const std::vector<SharedAbstractNode>& exprs, Context& ctxt);
    template SharedAbstractNode ConcatNode::create(const std::list<SharedAbstractNode>& exprs, Context& ctxt);
    template <class T>
    SharedAbstractNode ConcatNode::create(T const& exprs, Context& ctxt) {
      auto node = std::shared_ptr<ConcatNode>(new ConcatNode(ctxt));
      for (auto expr : exprs)
        node->addChild(expr);
      node->init();
      return node;
    }


    void ConcatNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("ConcatNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 0;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->size += this->children[index]->getBitvectorSize();
      }

      if (size > triton::max_bits_supported)
        throw triton::ast::exceptions::Ast("ConcatNode::init(): Size connot be greater than " + std::to_string(triton::max_bits_supported) + ".");

      this->eval = this->children[0]->evaluate();
      for (triton::uint32 index = 0; index < this->children.size()-1; index++)
        this->eval = ((this->eval << this->children[index+1]->getBitvectorSize()) | this->children[index+1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 ConcatNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Decimal node */


    DecimalNode::DecimalNode(Context& ctxt):
      AbstractNode(DECIMAL_NODE, ctxt)
    {}



    SharedAbstractNode DecimalNode::create(triton::uint512 value, Context& ctxt) {
      auto node = std::shared_ptr<DecimalNode>(new DecimalNode(ctxt));
      node->value = value;
      node->init();
      return node;
    }


    void DecimalNode::init(void) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;

      /* Init parents */
      updateParents();
    }


    triton::uint512 DecimalNode::getValue(void) {
      return this->value;
    }


    triton::uint512 DecimalNode::hash(triton::uint32) const {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== Distinct node */


    DistinctNode::DistinctNode(Context& ctxt):
      AbstractNode(DISTINCT_NODE, ctxt)
    {}



    SharedAbstractNode DistinctNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<DistinctNode>(new DistinctNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void DistinctNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("DistinctNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() != this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 DistinctNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== equal */


    EqualNode::EqualNode(Context& ctxt):
      AbstractNode(EQUAL_NODE, ctxt)
    {}



    SharedAbstractNode EqualNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<EqualNode>(new EqualNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    void EqualNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("EqualNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() == this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 EqualNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== extract */


    ExtractNode::ExtractNode(Context& ctxt):
      AbstractNode(EXTRACT_NODE, ctxt)
    {}



    SharedAbstractNode ExtractNode::create(triton::uint32 high, triton::uint32 low, SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<ExtractNode>(new ExtractNode(expr->getContext()));
      node->addChild(node->ctxt.decimal(high));
      node->addChild(node->ctxt.decimal(low));
      node->addChild(expr);
      node->init();
      return node;
    }


    void ExtractNode::init(void) {
      triton::uint32 high = 0;
      triton::uint32 low  = 0;

      if (this->children.size() < 3)
        throw triton::ast::exceptions::Ast("ExtractNode::init(): Must take at least three children.");

      if (this->children[0]->getKind() != DECIMAL_NODE || this->children[1]->getKind() != DECIMAL_NODE)
        throw triton::ast::exceptions::Ast("ExtractNode::init(): The highest and lower bit must be a DECIMAL_NODE.");

      high = reinterpret_cast<DecimalNode*>(this->children[0].get())->getValue().convert_to<triton::uint32>();
      low  = reinterpret_cast<DecimalNode*>(this->children[1].get())->getValue().convert_to<triton::uint32>();

      if (low > high)
        throw triton::ast::exceptions::Ast("ExtractNode::init(): The high bit must be greater than the low bit.");

      /* Init attributes */
      this->size = ((high - low) + 1);
      this->eval = ((this->children[2]->evaluate() >> low) & this->getBitvectorMask());

      if (this->size > this->children[2]->getBitvectorSize() || high >= this->children[2]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("ExtractNode::init(): The size of the extraction is higher than the child expression.");

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 ExtractNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== ite */


    IteNode::IteNode(Context& ctxt):
      AbstractNode(ITE_NODE, ctxt)
    {}



    SharedAbstractNode IteNode::create(SharedAbstractNode const& ifExpr, SharedAbstractNode const& thenExpr, SharedAbstractNode const& elseExpr) {
      auto node = std::shared_ptr<IteNode>(new IteNode(ifExpr->getContext()));
      node->addChild(ifExpr);
      node->addChild(thenExpr);
      node->addChild(elseExpr);
      node->init();
      return node;
    }


    void IteNode::init(void) {
      if (this->children.size() < 3)
        throw triton::ast::exceptions::Ast("IteNode::init(): Must take at least three children.");

      if (this->children[0]->isLogical() == false)
        throw triton::ast::exceptions::Ast("IteNode::init(): Must take a logical node as first argument.");

      if (this->children[1]->getBitvectorSize() != this->children[2]->getBitvectorSize())
        throw triton::ast::exceptions::Ast("IteNode::init(): Must take two nodes of same size as 'then' and 'else' branches.");

      /* Init attributes */
      this->size = this->children[1]->getBitvectorSize();
      this->eval = this->children[0]->evaluate() ? this->children[1]->evaluate() : this->children[2]->evaluate();

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 IteNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Land */


    LandNode::LandNode(Context& ctxt):
      AbstractNode(LAND_NODE, ctxt)
    {}



    SharedAbstractNode LandNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<LandNode>(new LandNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    template SharedAbstractNode LandNode::create(const std::vector<SharedAbstractNode>& exprs, Context& ctxt);
    template SharedAbstractNode LandNode::create(const std::list<SharedAbstractNode>& exprs, Context& ctxt);
    template <typename T>
    SharedAbstractNode LandNode::create(const T& exprs, Context& ctxt) {
      auto node = std::shared_ptr<LandNode>(new LandNode(ctxt));
      for (auto expr : exprs)
        node->addChild(expr);
      node->init();
      return node;
    }


    void LandNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("LandNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = 1;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = this->eval && this->children[index]->evaluate();

        if (this->children[index]->isLogical() == false)
          throw triton::ast::exceptions::Ast("LandNode::init(): Must take logical nodes as arguments.");
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 LandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Let */


    LetNode::LetNode(Context& ctxt):
      AbstractNode(LET_NODE, ctxt)
    {}



    SharedAbstractNode LetNode::create(std::string alias, SharedAbstractNode const& expr2, SharedAbstractNode const& expr3) {
      auto node = std::shared_ptr<LetNode>(new LetNode(expr2->getContext()));
      node->addChild(expr2->getContext().string(alias));
      node->addChild(expr2);
      node->addChild(expr3);
      node->init();
      return node;
    }


    void LetNode::init(void) {
      if (this->children.size() < 3)
        throw triton::ast::exceptions::Ast("LetNode::init(): Must take at least three children.");

      if (this->children[0]->getKind() != STRING_NODE)
        throw triton::ast::exceptions::Ast("LetNode::init(): The alias node must be a STRING_NODE.");

      /* Init attributes */
      this->size = this->children[2]->getBitvectorSize();
      this->eval = this->children[2]->evaluate();

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 LetNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lnot */


    LnotNode::LnotNode(Context& ctxt):
      AbstractNode(LNOT_NODE, ctxt)
    {}



    SharedAbstractNode LnotNode::create(SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<LnotNode>(new LnotNode(expr->getContext()));
      node->addChild(expr);
      node->init();
      return node;
    }


    void LnotNode::init(void) {
      if (this->children.size() < 1)
        throw triton::ast::exceptions::Ast("LnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 1;
      this->eval = !(this->children[0]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();

        if (this->children[index]->isLogical() == false)
          throw triton::ast::exceptions::Ast("LnotNode::init(): Must take logical nodes arguments.");
      }


      /* Init parents */
      updateParents();
    }


    triton::uint512 LnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lor */


    LorNode::LorNode(Context& ctxt):
      AbstractNode(LOR_NODE, ctxt)
    {}



    SharedAbstractNode LorNode::create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2) {
      auto node = std::shared_ptr<LorNode>(new LorNode(expr1->getContext()));
      node->addChild(expr1);
      node->addChild(expr2);
      node->init();
      return node;
    }


    template SharedAbstractNode LorNode::create(const std::vector<SharedAbstractNode>& exprs, Context& ctxt);
    template SharedAbstractNode LorNode::create(const std::list<SharedAbstractNode>& exprs, Context& ctxt);
    template <typename T>
    SharedAbstractNode LorNode::create(const T& exprs, Context& ctxt) {
      auto node = std::shared_ptr<LorNode>(new LorNode(ctxt));
      for (auto expr : exprs)
        node->addChild(expr);
      node->init();
      return node;
    }


    void LorNode::init(void) {
      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("LorNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = 0;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = this->eval || this->children[index]->evaluate();

        if (this->children[index]->isLogical() == false)
          throw triton::ast::exceptions::Ast("LorNode::init(): Must take logical nodes as arguments.");
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 LorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Reference node */


    ReferenceNode::ReferenceNode(SharedAbstractNode const& ast, size_t id, std::function<void()> const& end):
      AbstractNode(REFERENCE_NODE, ast->getContext()),
      id(id),
      ast(ast),
      end_(end)
    {}


    ReferenceNode::~ReferenceNode() {
      if(this->end_)
        this->end_();
    }


    SharedAbstractNode ReferenceNode::create(SharedAbstractNode const& ast, size_t id, std::function<void()> const& end) {
      auto node = std::shared_ptr<ReferenceNode>(new ReferenceNode(ast, id, end));
      // FIXME: use children to store ast
      ast->setParent(node.get());
      node->init();
      return node;
    }


    void ReferenceNode::init(void) {
      /* Init attributes */
      this->eval        = this->ast->evaluate();
      this->size        = this->ast->getBitvectorSize();
      this->symbolized  = this->ast->isSymbolized();

      /* Init parents */
      updateParents();
    }


    triton::uint512 ReferenceNode::hash(triton::uint32) const {
      triton::uint512 hash = this->kind ^ this->getId();
      return hash;
    }

    size_t ReferenceNode::getId() const
    {
      return this->id;
    }

    SharedAbstractNode const& ReferenceNode::getAst()
    {
      return this->ast;
    }

    /* ====== String node */


    StringNode::StringNode(std::string value, Context& ctxt):
      AbstractNode(STRING_NODE, ctxt),
      value(value)
    {}



    SharedAbstractNode StringNode::create(std::string value, Context& ctxt) {
      auto node = std::shared_ptr<StringNode>(new StringNode(value, ctxt));
      node->init();
      return node;
    }


    void StringNode::init(void) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;

      /* Init parents */
      updateParents();
    }


    std::string StringNode::getValue(void) {
      return this->value;
    }


    triton::uint512 StringNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::const_iterator it=this->value.cbegin(); it != this->value.cend(); it++)
        h = h ^ triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== sx */


    SxNode::SxNode(Context& ctxt):
      AbstractNode(SX_NODE, ctxt)
    {}



    SharedAbstractNode SxNode::create(triton::uint32 sizeExt, SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<SxNode>(new SxNode(expr->getContext()));
      node->addChild(node->ctxt.decimal(sizeExt));
      node->addChild(expr);
      node->init();
      return node;
    }


    void SxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("SxNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::ast::exceptions::Ast("SxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->children[0].get())->getValue().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->children[1]->getBitvectorSize();
      if (size > triton::max_bits_supported)
        throw triton::ast::exceptions::Ast("SxNode::SxNode(): Size connot be greater than " + std::to_string(triton::max_bits_supported) + ".");

      this->eval = ((((this->children[1]->evaluate() >> (this->children[1]->getBitvectorSize()-1)) == 0) ? this->children[1]->evaluate() : (this->children[1]->evaluate() | ~(this->children[1]->getBitvectorMask()))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 SxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Variable node */


    // FIXME: It would be more efficient to have id
    VariableNode::VariableNode(std::string const& varName, Context& ctxt)
      : AbstractNode(VARIABLE_NODE, ctxt),
        varName(varName)
    {}



    SharedAbstractNode VariableNode::create(std::string const& varName, triton::uint32 size, Context& ctxt) {
      auto node = std::shared_ptr<VariableNode>(new VariableNode(varName, ctxt));
      node->setBitvectorSize(size);
      ctxt.initVariable(varName, 0, node);
      node->symbolized  = true;
      node->init();
      return node;
    }


    void VariableNode::init(void) {
      this->eval        = ctxt.getValueForVariable(this->varName) & this->getBitvectorMask();

      /* Init parents */
      updateParents();
    }


    std::string const& VariableNode::getVarName() const {
      return this->varName;
    }


    triton::uint512 VariableNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;

      for (char c : this->varName)
        h = h ^ triton::ast::pow(c, index++);

      return triton::ast::rotl(h, deep);
    }


    /* ====== zx */


    ZxNode::ZxNode(Context& ctxt):
      AbstractNode(ZX_NODE, ctxt)
    {}



    SharedAbstractNode ZxNode::create(triton::uint32 sizeExt, SharedAbstractNode const& expr) {
      auto node = std::shared_ptr<ZxNode>(new ZxNode(expr->getContext()));
      node->addChild(node->ctxt.decimal(sizeExt));
      node->addChild(expr);
      node->init();
      return node;
    }


    void ZxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::ast::exceptions::Ast("ZxNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::ast::exceptions::Ast("ZxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->children[0].get())->getValue().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->children[1]->getBitvectorSize();
      if (size > triton::max_bits_supported)
        throw triton::ast::exceptions::Ast("ZxNode::init(): Size connot be greater than " + std::to_string(triton::max_bits_supported) + ".");

      this->eval = (this->children[1]->evaluate() & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      updateParents();
    }


    triton::uint512 ZxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }

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

    triton::uint512 pow(triton::uint512 hash, triton::uint32 n) {
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



/* ====== Node builders */

namespace triton {
  namespace ast {

    SharedAbstractNode newInstance(AbstractNode* node) {
      SharedAbstractNode newNode = nullptr;

      if (node == nullptr)
        return nullptr;

      switch (node->getKind()) {
        case BVADD_NODE:                newNode.reset(new(std::nothrow) BvaddNode(*reinterpret_cast<BvaddNode*>(node))); break;
        case BVAND_NODE:                newNode.reset(new(std::nothrow) BvandNode(*reinterpret_cast<BvandNode*>(node))); break;
        case BVASHR_NODE:               newNode.reset(new(std::nothrow) BvashrNode(*reinterpret_cast<BvashrNode*>(node))); break;
        case BVLSHR_NODE:               newNode.reset(new(std::nothrow) BvlshrNode(*reinterpret_cast<BvlshrNode*>(node))); break;
        case BVMUL_NODE:                newNode.reset(new(std::nothrow) BvmulNode(*reinterpret_cast<BvmulNode*>(node))); break;
        case BVNAND_NODE:               newNode.reset(new(std::nothrow) BvnandNode(*reinterpret_cast<BvnandNode*>(node))); break;
        case BVNEG_NODE:                newNode.reset(new(std::nothrow) BvnegNode(*reinterpret_cast<BvnegNode*>(node))); break;
        case BVNOR_NODE:                newNode.reset(new(std::nothrow) BvnorNode(*reinterpret_cast<BvnorNode*>(node))); break;
        case BVNOT_NODE:                newNode.reset(new(std::nothrow) BvnotNode(*reinterpret_cast<BvnotNode*>(node))); break;
        case BVOR_NODE:                 newNode.reset(new(std::nothrow) BvorNode(*reinterpret_cast<BvorNode*>(node))); break;
        case BVROL_NODE:                newNode.reset(new(std::nothrow) BvrolNode(*reinterpret_cast<BvrolNode*>(node))); break;
        case BVROR_NODE:                newNode.reset(new(std::nothrow) BvrorNode(*reinterpret_cast<BvrorNode*>(node))); break;
        case BVSDIV_NODE:               newNode.reset(new(std::nothrow) BvsdivNode(*reinterpret_cast<BvsdivNode*>(node))); break;
        case BVSGE_NODE:                newNode.reset(new(std::nothrow) BvsgeNode(*reinterpret_cast<BvsgeNode*>(node))); break;
        case BVSGT_NODE:                newNode.reset(new(std::nothrow) BvsgtNode(*reinterpret_cast<BvsgtNode*>(node))); break;
        case BVSHL_NODE:                newNode.reset(new(std::nothrow) BvshlNode(*reinterpret_cast<BvshlNode*>(node))); break;
        case BVSLE_NODE:                newNode.reset(new(std::nothrow) BvsleNode(*reinterpret_cast<BvsleNode*>(node))); break;
        case BVSLT_NODE:                newNode.reset(new(std::nothrow) BvsltNode(*reinterpret_cast<BvsltNode*>(node))); break;
        case BVSMOD_NODE:               newNode.reset(new(std::nothrow) BvsmodNode(*reinterpret_cast<BvsmodNode*>(node))); break;
        case BVSREM_NODE:               newNode.reset(new(std::nothrow) BvsremNode(*reinterpret_cast<BvsremNode*>(node))); break;
        case BVSUB_NODE:                newNode.reset(new(std::nothrow) BvsubNode(*reinterpret_cast<BvsubNode*>(node))); break;
        case BVUDIV_NODE:               newNode.reset(new(std::nothrow) BvudivNode(*reinterpret_cast<BvudivNode*>(node))); break;
        case BVUGE_NODE:                newNode.reset(new(std::nothrow) BvugeNode(*reinterpret_cast<BvugeNode*>(node))); break;
        case BVUGT_NODE:                newNode.reset(new(std::nothrow) BvugtNode(*reinterpret_cast<BvugtNode*>(node))); break;
        case BVULE_NODE:                newNode.reset(new(std::nothrow) BvuleNode(*reinterpret_cast<BvuleNode*>(node))); break;
        case BVULT_NODE:                newNode.reset(new(std::nothrow) BvultNode(*reinterpret_cast<BvultNode*>(node))); break;
        case BVUREM_NODE:               newNode.reset(new(std::nothrow) BvuremNode(*reinterpret_cast<BvuremNode*>(node))); break;
        case BVXNOR_NODE:               newNode.reset(new(std::nothrow) BvxnorNode(*reinterpret_cast<BvxnorNode*>(node))); break;
        case BVXOR_NODE:                newNode.reset(new(std::nothrow) BvxorNode(*reinterpret_cast<BvxorNode*>(node))); break;
        case BV_NODE:                   newNode.reset(new(std::nothrow) BvNode(*reinterpret_cast<BvNode*>(node))); break;
        case CONCAT_NODE:               newNode.reset(new(std::nothrow) ConcatNode(*reinterpret_cast<ConcatNode*>(node))); break;
        case DECIMAL_NODE:              newNode.reset(new(std::nothrow) DecimalNode(*reinterpret_cast<DecimalNode*>(node))); break;
        case DISTINCT_NODE:             newNode.reset(new(std::nothrow) DistinctNode(*reinterpret_cast<DistinctNode*>(node))); break;
        case EQUAL_NODE:                newNode.reset(new(std::nothrow) EqualNode(*reinterpret_cast<EqualNode*>(node))); break;
        case EXTRACT_NODE:              newNode.reset(new(std::nothrow) ExtractNode(*reinterpret_cast<ExtractNode*>(node))); break;
        case ITE_NODE:                  newNode.reset(new(std::nothrow) IteNode(*reinterpret_cast<IteNode*>(node))); break;
        case LAND_NODE:                 newNode.reset(new(std::nothrow) LandNode(*reinterpret_cast<LandNode*>(node))); break;
        case LET_NODE:                  newNode.reset(new(std::nothrow) LetNode(*reinterpret_cast<LetNode*>(node))); break;
        case LNOT_NODE:                 newNode.reset(new(std::nothrow) LnotNode(*reinterpret_cast<LnotNode*>(node))); break;
        case LOR_NODE:                  newNode.reset(new(std::nothrow) LorNode(*reinterpret_cast<LorNode*>(node))); break;
        case REFERENCE_NODE:            newNode.reset(new(std::nothrow) ReferenceNode(*reinterpret_cast<ReferenceNode*>(node))); break;
        case STRING_NODE:               newNode.reset(new(std::nothrow) StringNode(*reinterpret_cast<StringNode*>(node))); break;
        case SX_NODE:                   newNode.reset(new(std::nothrow) SxNode(*reinterpret_cast<SxNode*>(node))); break;
        case VARIABLE_NODE:             newNode.reset(new(std::nothrow) VariableNode(*reinterpret_cast<VariableNode*>(node))); break;
        case ZX_NODE:                   newNode.reset(new(std::nothrow) ZxNode(*reinterpret_cast<ZxNode*>(node))); break;
        default:
          throw triton::ast::exceptions::Ast("triton::ast::newInstance(): Invalid kind node.");
      }

      if (newNode == nullptr)
        throw triton::ast::exceptions::Ast("triton::ast::newInstance(): No enough memory.");

      return newNode;
    }

  }; /* ast namespace */
}; /* triton namespace */

