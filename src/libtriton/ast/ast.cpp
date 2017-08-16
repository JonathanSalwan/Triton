//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cmath>
#include <new>

#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/exceptions.hpp>
#include <triton/tritonToZ3Ast.hpp>



namespace triton {
  namespace ast {

    /* ====== Abstract node */

    AbstractNode::AbstractNode(enum kind_e kind, AstContext& ctxt): ctxt(ctxt) {
      this->eval        = 0;
      this->kind        = kind;
      this->size        = 0;
      this->symbolized  = false;
    }

    AbstractNode::AbstractNode(const AbstractNode& copy, AstContext& ctxt): ctxt(ctxt) {
      this->eval        = copy.eval;
      this->kind        = copy.kind;
      this->parents     = copy.parents;
      this->size        = copy.size;
      this->symbolized  = copy.symbolized;

      for (triton::uint32 index = 0; index < copy.children.size(); index++)
        this->children.push_back(triton::ast::newInstance(copy.children[index]));
    }


    AbstractNode::~AbstractNode() {
      /* virtual */
    }


    AstContext& AbstractNode::getContext(void) const {
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


    std::vector<AbstractNode*>& AbstractNode::getChildren(void) {
      return this->children;
    }


    std::set<AbstractNode*>& AbstractNode::getParents(void) {
      return this->parents;
    }


    void AbstractNode::setParent(AbstractNode* p) {
      this->parents.insert(p);
    }


    void AbstractNode::removeParent(AbstractNode* p) {
      this->parents.erase(p);
    }


    void AbstractNode::setParent(std::set<AbstractNode*>& p) {
      for (std::set<AbstractNode*>::iterator it = p.begin(); it != p.end(); it++)
        this->parents.insert(*it);
    }


    void AbstractNode::addChild(AbstractNode* child) {
      this->children.push_back(child);
    }


    void AbstractNode::setChild(triton::uint32 index, AbstractNode* child) {
      if (index >= this->children.size())
        throw triton::exceptions::Ast("AbstractNode::setChild(): Invalid index.");

      if (child == nullptr)
        throw triton::exceptions::Ast("AbstractNode::setChild(): child cannot be null.");

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


    BvaddNode::BvaddNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVADD_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvaddNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvand */


    BvandNode::BvandNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }



    /* ====== bvashr (shift with sign extension fill) */


    BvashrNode::BvashrNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVASHR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvashrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvlshr (shift with zero filled) */


    BvlshrNode::BvlshrNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVLSHR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvlshrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvmul */


    BvmulNode::BvmulNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVMUL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvmulNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnand */


    BvnandNode::BvnandNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVNAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvnandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvneg */


    BvnegNode::BvnegNode(AbstractNode* expr): AbstractNode(BVNEG_NODE, expr->getContext()) {
      this->addChild(expr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvnegNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnor */


    BvnorNode::BvnorNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVNOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnot */


    BvnotNode::BvnotNode(AbstractNode* expr): AbstractNode(BVNOT_NODE, expr->getContext()) {
      this->addChild(expr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvor */


    BvorNode::BvorNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvrol */


    BvrolNode::BvrolNode(triton::uint32 rot, AbstractNode* expr): BvrolNode(expr->getContext().decimal(rot), expr) {
    }


    BvrolNode::BvrolNode(AbstractNode* rot, AbstractNode* expr): AbstractNode(BVROL_NODE, rot->getContext()) {
      this->addChild(rot);
      this->addChild(expr);
      this->init();
    }


    void BvrolNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvrolNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvrolNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->children[0])->getValue().convert_to<triton::uint32>();
      value = this->children[1]->evaluate();

      /* Init attributes */
      this->size = this->children[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value << rot) | (value >> (this->size - rot))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvrolNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvror */


    BvrorNode::BvrorNode(triton::uint32 rot, AbstractNode* expr): BvrorNode(expr->getContext().decimal(rot), expr) {
    }


    BvrorNode::BvrorNode(AbstractNode* rot, AbstractNode* expr): AbstractNode(BVROR_NODE, expr->getContext()) {
      this->addChild(rot);
      this->addChild(expr);
      this->init();
    }


    void BvrorNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvrorNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvrorNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->children[0])->getValue().convert_to<triton::uint32>();
      value = this->children[1]->evaluate();

      /* Init attributes */
      this->size = this->children[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value >> rot) | (value << (this->size - rot))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvrorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsdiv */


    BvsdivNode::BvsdivNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSDIV_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void BvsdivNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsdivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsge */


    BvsgeNode::BvsgeNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSGE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void BvsgeNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed >= op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsgeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsgt */


    BvsgtNode::BvsgtNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSGT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void BvsgtNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed > op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsgtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvshl */


    BvshlNode::BvshlNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSHL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvshlNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsle */


    BvsleNode::BvsleNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSLE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }

    void BvsleNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsleNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed <= op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvslt */


    BvsltNode::BvsltNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSLT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void BvsltNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsltNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsltNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed < op2Signed);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsltNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsmod - 2's complement signed remainder (sign follows divisor) */


    BvsmodNode::BvsmodNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSMOD_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void BvsmodNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsmodNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsrem - 2's complement signed remainder (sign follows dividend) */


    BvsremNode::BvsremNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSREM_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void BvsremNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsremNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0]);
      op2Signed = triton::ast::modularSignExtend(this->children[1]);

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsub */


    BvsubNode::BvsubNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVSUB_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvsubNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvudiv */


    BvudivNode::BvudivNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVUDIV_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvudivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvuge */


    BvugeNode::BvugeNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVUGE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvugeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvugt */


    BvugtNode::BvugtNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVUGT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvugtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvule */


    BvuleNode::BvuleNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVULE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvuleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvult */


    BvultNode::BvultNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVULT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvultNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvurem */


    BvuremNode::BvuremNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVUREM_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvuremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxnor */


    BvxnorNode::BvxnorNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVXNOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvxnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxor */


    BvxorNode::BvxorNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(BVXOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvxorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bv */


    BvNode::BvNode(triton::uint512 value, triton::uint32 size, AstContext& ctxt): AbstractNode(BV_NODE, ctxt) {
      this->addChild(ctxt.decimal(value));
      this->addChild(ctxt.decimal(size));
      this->init();
    }


    void BvNode::init(void) {
      triton::uint512 value = 0;
      triton::uint32 size   = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE || this->children[1]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvNode::init(): Size and value must be a DECIMAL_NODE.");

      value = reinterpret_cast<DecimalNode*>(this->children[0])->getValue();
      size  = reinterpret_cast<DecimalNode*>(this->children[1])->getValue().convert_to<triton::uint32>();

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 BvNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== concat */


    ConcatNode::ConcatNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(CONCAT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    template ConcatNode::ConcatNode(const std::vector<AbstractNode*>& exprs, AstContext& ctxt);
    template ConcatNode::ConcatNode(const std::list<AbstractNode*>& exprs, AstContext& ctxt);
    template <typename T>
    ConcatNode::ConcatNode(const T& exprs, AstContext& ctxt): AbstractNode(CONCAT_NODE, ctxt) {
      for (AbstractNode* expr : exprs)
        this->addChild(expr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 ConcatNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Decimal node */


    DecimalNode::DecimalNode(triton::uint512 value, AstContext& ctxt): AbstractNode(DECIMAL_NODE, ctxt) {
      this->value = value;
      this->init();
    }


    void DecimalNode::init(void) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 DecimalNode::getValue(void) {
      return this->value;
    }


    triton::uint512 DecimalNode::hash(triton::uint32 deep) const {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== Distinct node */


    DistinctNode::DistinctNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(DISTINCT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void DistinctNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("DistinctNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() != this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 DistinctNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== equal */


    EqualNode::EqualNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(EQUAL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    void EqualNode::init(void) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("EqualNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->children[0]->evaluate() == this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 EqualNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== extract */


    ExtractNode::ExtractNode(triton::uint32 high, triton::uint32 low, AbstractNode* expr): AbstractNode(EXTRACT_NODE, expr->getContext()) {
      this->addChild(this->ctxt.decimal(high));
      this->addChild(this->ctxt.decimal(low));
      this->addChild(expr);
      this->init();
    }


    void ExtractNode::init(void) {
      triton::uint32 high = 0;
      triton::uint32 low  = 0;

      if (this->children.size() < 3)
        throw triton::exceptions::Ast("ExtractNode::init(): Must take at least three children.");

      if (this->children[0]->getKind() != DECIMAL_NODE || this->children[1]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("ExtractNode::init(): The highest and lower bit must be a DECIMAL_NODE.");

      high = reinterpret_cast<DecimalNode*>(this->children[0])->getValue().convert_to<triton::uint32>();
      low  = reinterpret_cast<DecimalNode*>(this->children[1])->getValue().convert_to<triton::uint32>();

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 ExtractNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== ite */


    IteNode::IteNode(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr): AbstractNode(ITE_NODE, ifExpr->getContext()) {
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 IteNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Land */


    LandNode::LandNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(LAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    template LandNode::LandNode(const std::vector<AbstractNode*>& exprs, AstContext& ctxt);
    template LandNode::LandNode(const std::list<AbstractNode*>& exprs, AstContext& ctxt);
    template <typename T>
    LandNode::LandNode(const T& exprs, AstContext& ctxt): AbstractNode(LAND_NODE, ctxt) {
      for (AbstractNode* expr : exprs)
        this->addChild(expr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 LandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Let */


    LetNode::LetNode(std::string alias, AbstractNode* expr2, AbstractNode* expr3): AbstractNode(LET_NODE, expr2->getContext()) {
      this->addChild(ctxt.string(alias));
      this->addChild(expr2);
      this->addChild(expr3);
      this->init();
    }


    void LetNode::init(void) {
      if (this->children.size() < 3)
        throw triton::exceptions::Ast("LetNode::init(): Must take at least three children.");

      if (this->children[0]->getKind() != STRING_NODE)
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 LetNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lnot */


    LnotNode::LnotNode(AbstractNode* expr): AbstractNode(LNOT_NODE, expr->getContext()) {
      this->addChild(expr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 LnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lor */


    LorNode::LorNode(AbstractNode* expr1, AbstractNode* expr2): AbstractNode(LOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    template LorNode::LorNode(const std::vector<AbstractNode*>& exprs, AstContext& ctxt);
    template LorNode::LorNode(const std::list<AbstractNode*>& exprs, AstContext& ctxt);
    template <typename T>
    LorNode::LorNode(const T& exprs, AstContext& ctxt): AbstractNode(LOR_NODE, ctxt) {
      for (AbstractNode* expr : exprs)
        this->addChild(expr);
      this->init();
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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 LorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * this->children[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Reference node */


    ReferenceNode::ReferenceNode(triton::engines::symbolic::SymbolicExpression& expr)
      : AbstractNode(REFERENCE_NODE, expr.getAst()->getContext())
      , expr(expr) {
      this->init();
    }


    void ReferenceNode::init(void) {
      /* Init attributes */
      this->eval        = this->expr.getAst()->evaluate();
      this->size        = this->expr.getAst()->getBitvectorSize();
      this->symbolized  = this->expr.getAst()->isSymbolized();

      this->expr.getAst()->setParent(this);

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 ReferenceNode::hash(triton::uint32 deep) const {
      triton::uint512 hash = this->kind ^ this->expr.getId();
      return hash;
    }


    triton::engines::symbolic::SymbolicExpression& ReferenceNode::getSymbolicExpression(void) const {
      return this->expr;
    }


    /* ====== String node */


    StringNode::StringNode(std::string value, AstContext& ctxt): AbstractNode(STRING_NODE, ctxt) {
      this->value = value;
      this->init();
    }


    void StringNode::init(void) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->symbolized  = false;

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
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


    SxNode::SxNode(triton::uint32 sizeExt, AbstractNode* expr): AbstractNode(SX_NODE, expr->getContext()) {
      this->addChild(ctxt.decimal(sizeExt));
      this->addChild(expr);
      this->init();
    }


    void SxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("SxNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("SxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->children[0])->getValue().convert_to<triton::uint32>();

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::uint512 SxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->children.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++)
        h = h * triton::ast::pow(this->children[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Variable node */


    // WARNING: A variable ast node should not live once the SymbolicVariable is dead
    VariableNode::VariableNode(triton::engines::symbolic::SymbolicVariable& symVar, AstContext& ctxt)
      : AbstractNode(VARIABLE_NODE, ctxt),
        symVar(symVar) {
      ctxt.initVariable(symVar.getName(), 0);
      this->init();
    }


    void VariableNode::init(void) {
      this->size        = this->symVar.getSize();
      this->eval        = ctxt.getValueForVariable(this->symVar.getName()) & this->getBitvectorMask();
      this->symbolized  = true;

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::engines::symbolic::SymbolicVariable& VariableNode::getVar() {
      return this->symVar;
    }


    triton::uint512 VariableNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;

      for (char c : this->symVar.getName())
        h = h ^ triton::ast::pow(c, index++);

      return triton::ast::rotl(h, deep);
    }


    /* ====== zx */


    ZxNode::ZxNode(triton::uint32 sizeExt, AbstractNode* expr): AbstractNode(ZX_NODE, expr->getContext()) {
      this->addChild(ctxt.decimal(sizeExt));
      this->addChild(expr);
      this->init();
    }


    void ZxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("ZxNode::init(): Must take at least two children.");

      if (this->children[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("ZxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->children[0])->getValue().convert_to<triton::uint32>();

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
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
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
      return triton::ast::representations::astRepresentation.print(stream, node);
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

    AbstractNode* newInstance(AbstractNode* node) {
      AbstractNode* newNode = nullptr;

      if (node == nullptr)
        return nullptr;

      switch (node->getKind()) {
        case BVADD_NODE:                newNode = new(std::nothrow) BvaddNode(*reinterpret_cast<BvaddNode*>(node)); break;
        case BVAND_NODE:                newNode = new(std::nothrow) BvandNode(*reinterpret_cast<BvandNode*>(node)); break;
        case BVASHR_NODE:               newNode = new(std::nothrow) BvashrNode(*reinterpret_cast<BvashrNode*>(node)); break;
        case BVLSHR_NODE:               newNode = new(std::nothrow) BvlshrNode(*reinterpret_cast<BvlshrNode*>(node)); break;
        case BVMUL_NODE:                newNode = new(std::nothrow) BvmulNode(*reinterpret_cast<BvmulNode*>(node)); break;
        case BVNAND_NODE:               newNode = new(std::nothrow) BvnandNode(*reinterpret_cast<BvnandNode*>(node)); break;
        case BVNEG_NODE:                newNode = new(std::nothrow) BvnegNode(*reinterpret_cast<BvnegNode*>(node)); break;
        case BVNOR_NODE:                newNode = new(std::nothrow) BvnorNode(*reinterpret_cast<BvnorNode*>(node)); break;
        case BVNOT_NODE:                newNode = new(std::nothrow) BvnotNode(*reinterpret_cast<BvnotNode*>(node)); break;
        case BVOR_NODE:                 newNode = new(std::nothrow) BvorNode(*reinterpret_cast<BvorNode*>(node)); break;
        case BVROL_NODE:                newNode = new(std::nothrow) BvrolNode(*reinterpret_cast<BvrolNode*>(node)); break;
        case BVROR_NODE:                newNode = new(std::nothrow) BvrorNode(*reinterpret_cast<BvrorNode*>(node)); break;
        case BVSDIV_NODE:               newNode = new(std::nothrow) BvsdivNode(*reinterpret_cast<BvsdivNode*>(node)); break;
        case BVSGE_NODE:                newNode = new(std::nothrow) BvsgeNode(*reinterpret_cast<BvsgeNode*>(node)); break;
        case BVSGT_NODE:                newNode = new(std::nothrow) BvsgtNode(*reinterpret_cast<BvsgtNode*>(node)); break;
        case BVSHL_NODE:                newNode = new(std::nothrow) BvshlNode(*reinterpret_cast<BvshlNode*>(node)); break;
        case BVSLE_NODE:                newNode = new(std::nothrow) BvsleNode(*reinterpret_cast<BvsleNode*>(node)); break;
        case BVSLT_NODE:                newNode = new(std::nothrow) BvsltNode(*reinterpret_cast<BvsltNode*>(node)); break;
        case BVSMOD_NODE:               newNode = new(std::nothrow) BvsmodNode(*reinterpret_cast<BvsmodNode*>(node)); break;
        case BVSREM_NODE:               newNode = new(std::nothrow) BvsremNode(*reinterpret_cast<BvsremNode*>(node)); break;
        case BVSUB_NODE:                newNode = new(std::nothrow) BvsubNode(*reinterpret_cast<BvsubNode*>(node)); break;
        case BVUDIV_NODE:               newNode = new(std::nothrow) BvudivNode(*reinterpret_cast<BvudivNode*>(node)); break;
        case BVUGE_NODE:                newNode = new(std::nothrow) BvugeNode(*reinterpret_cast<BvugeNode*>(node)); break;
        case BVUGT_NODE:                newNode = new(std::nothrow) BvugtNode(*reinterpret_cast<BvugtNode*>(node)); break;
        case BVULE_NODE:                newNode = new(std::nothrow) BvuleNode(*reinterpret_cast<BvuleNode*>(node)); break;
        case BVULT_NODE:                newNode = new(std::nothrow) BvultNode(*reinterpret_cast<BvultNode*>(node)); break;
        case BVUREM_NODE:               newNode = new(std::nothrow) BvuremNode(*reinterpret_cast<BvuremNode*>(node)); break;
        case BVXNOR_NODE:               newNode = new(std::nothrow) BvxnorNode(*reinterpret_cast<BvxnorNode*>(node)); break;
        case BVXOR_NODE:                newNode = new(std::nothrow) BvxorNode(*reinterpret_cast<BvxorNode*>(node)); break;
        case BV_NODE:                   newNode = new(std::nothrow) BvNode(*reinterpret_cast<BvNode*>(node)); break;
        case CONCAT_NODE:               newNode = new(std::nothrow) ConcatNode(*reinterpret_cast<ConcatNode*>(node)); break;
        case DECIMAL_NODE:              newNode = new(std::nothrow) DecimalNode(*reinterpret_cast<DecimalNode*>(node)); break;
        case DISTINCT_NODE:             newNode = new(std::nothrow) DistinctNode(*reinterpret_cast<DistinctNode*>(node)); break;
        case EQUAL_NODE:                newNode = new(std::nothrow) EqualNode(*reinterpret_cast<EqualNode*>(node)); break;
        case EXTRACT_NODE:              newNode = new(std::nothrow) ExtractNode(*reinterpret_cast<ExtractNode*>(node)); break;
        case ITE_NODE:                  newNode = new(std::nothrow) IteNode(*reinterpret_cast<IteNode*>(node)); break;
        case LAND_NODE:                 newNode = new(std::nothrow) LandNode(*reinterpret_cast<LandNode*>(node)); break;
        case LET_NODE:                  newNode = new(std::nothrow) LetNode(*reinterpret_cast<LetNode*>(node)); break;
        case LNOT_NODE:                 newNode = new(std::nothrow) LnotNode(*reinterpret_cast<LnotNode*>(node)); break;
        case LOR_NODE:                  newNode = new(std::nothrow) LorNode(*reinterpret_cast<LorNode*>(node)); break;
        case REFERENCE_NODE:            newNode = new(std::nothrow) ReferenceNode(*reinterpret_cast<ReferenceNode*>(node)); break;
        case STRING_NODE:               newNode = new(std::nothrow) StringNode(*reinterpret_cast<StringNode*>(node)); break;
        case SX_NODE:                   newNode = new(std::nothrow) SxNode(*reinterpret_cast<SxNode*>(node)); break;
        case VARIABLE_NODE:             newNode = new(std::nothrow) VariableNode(*reinterpret_cast<VariableNode*>(node)); break;
        case ZX_NODE:                   newNode = new(std::nothrow) ZxNode(*reinterpret_cast<ZxNode*>(node)); break;
        default:
          throw triton::exceptions::Ast("triton::ast::newInstance(): Invalid kind node.");
      }

      if (newNode == nullptr)
        throw triton::exceptions::Ast("triton::ast::newInstance(): No enough memory.");

      return node->getContext().getAstGarbageCollector().recordAstNode(newNode);
    }

  }; /* ast namespace */
}; /* triton namespace */

