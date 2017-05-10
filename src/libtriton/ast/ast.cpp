//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cmath>
#include <new>

#include <triton/api.hpp>
#include <triton/ast.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/exceptions.hpp>
#include <triton/tritonToZ3Ast.hpp>
#include <triton/z3Result.hpp>



namespace triton {
  namespace ast {

    /* ====== Abstract node */

    AbstractNode::AbstractNode(enum kind_e kind) {
      this->eval        = 0;
      this->kind        = kind;
      this->size        = 0;
      this->symbolized  = false;
    }


    AbstractNode::AbstractNode() {
      this->eval        = 0;
      this->kind        = UNDEFINED_NODE;
      this->size        = 0;
      this->symbolized  = false;
    }


    AbstractNode::AbstractNode(const AbstractNode& copy) {
      this->eval        = copy.eval;
      this->kind        = copy.kind;
      this->parents     = copy.parents;
      this->size        = copy.size;
      this->symbolized  = copy.symbolized;

      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(triton::ast::newInstance(copy.childs[index]));
    }


    AbstractNode::~AbstractNode() {
      /* virtual */
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


    std::vector<AbstractNode*>& AbstractNode::getChilds(void) {
      return this->childs;
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
      this->childs.push_back(child);
    }


    void AbstractNode::setChild(triton::uint32 index, AbstractNode* child) {
      if (index >= this->childs.size())
        throw triton::exceptions::Ast("AbstractNode::setChild(): Invalid index.");

      if (child == nullptr)
        throw triton::exceptions::Ast("AbstractNode::setChild(): child cannot be null.");

      /* Setup the parent of the child */
      child->setParent(this);

      /* Remove the parent of the old child */
      this->childs[index]->removeParent(this);

      /* Setup the child of the parent */
      this->childs[index] = child;
    }


    void AbstractNode::setBitvectorSize(triton::uint32 size) {
      this->size = size;
    }


    /* ====== assert */


    AssertNode::AssertNode(AbstractNode* expr) {
      this->kind = ASSERT_NODE;
      this->addChild(expr);
      this->init();
    }


    AssertNode::AssertNode(const AssertNode& copy) : AbstractNode(copy) {
    }


    AssertNode::~AssertNode() {
    }


    void AssertNode::init(void) {
      if (this->childs.size() < 1)
        throw triton::exceptions::Ast("AssertNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 1;
      this->eval = 0;

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void AssertNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 AssertNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvadd */


    BvaddNode::BvaddNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVADD_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvaddNode::BvaddNode(const BvaddNode& copy) : AbstractNode(copy) {
    }


    BvaddNode::~BvaddNode() {
    }


    void BvaddNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvaddNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvaddNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() + this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvaddNode::accept(AstVisitor& v) {
       v(*this);
    }


    triton::uint512 BvaddNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvand */


    BvandNode::BvandNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVAND_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvandNode::BvandNode(const BvandNode& copy) : AbstractNode(copy) {
    }


    BvandNode::~BvandNode() {
    }


    void BvandNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvandNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() & this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }



    /* ====== bvashr (shift with sign extension fill) */


    BvashrNode::BvashrNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVASHR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvashrNode::BvashrNode(const BvashrNode& copy) : AbstractNode(copy) {
    }


    BvashrNode::~BvashrNode() {
    }


    void BvashrNode::init(void) {
      triton::uint32 shift  = 0;
      triton::uint512 mask  = 0;
      triton::uint512 value = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvashrNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvashrNode::init(): Must take two nodes of same size.");

      value = this->childs[0]->evaluate();
      shift = this->childs[1]->evaluate().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      /* Mask based on the sign */
      if (this->childs[0]->isSigned()) {
        mask = 1;
        mask = ((mask << (this->size-1)) & this->getBitvectorMask());
      }

      if (shift >= this->size && this->childs[0]->isSigned()) {
        this->eval = -1;
        this->eval &= this->getBitvectorMask();
      }

      else if (shift >= this->size && !this->childs[0]->isSigned()) {
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

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


   void BvashrNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvashrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvdecl */


    BvdeclNode::BvdeclNode(triton::uint32 size) {
      this->kind = BVDECL_NODE;
      this->addChild(triton::ast::decimal(size));
      this->init();
    }


    BvdeclNode::BvdeclNode(const BvdeclNode& copy) : AbstractNode(copy) {
    }


    BvdeclNode::~BvdeclNode() {
    }


    void BvdeclNode::init(void) {
      triton::uint32 size = 0;

      if (this->childs.size() < 1)
        throw triton::exceptions::Ast("BvdeclNode::init(): Must take at least one child.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvdeclNode::init(): Child must be a DECIMAL_NODE.");

      size = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      if (!size)
        throw triton::exceptions::Ast("BvdeclNode::init(): Size connot be equal to zero.");

      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("BvdeclNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      /* Init attributes */
      this->size = size;
      this->eval = 0;

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvdeclNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvdeclNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvlshr (shift with zero filled) */


    BvlshrNode::BvlshrNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVLSHR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvlshrNode::BvlshrNode(const BvlshrNode& copy) : AbstractNode(copy) {
    }


    BvlshrNode::~BvlshrNode() {
    }


    void BvlshrNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvlshrNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvlshrNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() >> this->childs[1]->evaluate().convert_to<triton::uint32>());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvlshrNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvlshrNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvmul */


    BvmulNode::BvmulNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVMUL_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvmulNode::BvmulNode(const BvmulNode& copy) : AbstractNode(copy) {
    }


    BvmulNode::~BvmulNode() {
    }


    void BvmulNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvmulNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvmulNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() * this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvmulNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvmulNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnand */


    BvnandNode::BvnandNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVNAND_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvnandNode::BvnandNode(const BvnandNode& copy) : AbstractNode(copy) {
    }


    BvnandNode::~BvnandNode() {
    }


    void BvnandNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvnandNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvnandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~(this->childs[0]->evaluate() & this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvnandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvneg */


    BvnegNode::BvnegNode(AbstractNode* expr) {
      this->kind = BVNEG_NODE;
      this->addChild(expr);
      this->init();
    }


    BvnegNode::BvnegNode(const BvnegNode& copy) : AbstractNode(copy) {
    }


    BvnegNode::~BvnegNode() {
    }


    void BvnegNode::init(void) {
      if (this->childs.size() < 1)
        throw triton::exceptions::Ast("BvnegNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((-(this->childs[0]->evaluate().convert_to<triton::sint512>())).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvnegNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnegNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnor */


    BvnorNode::BvnorNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVNOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvnorNode::BvnorNode(const BvnorNode& copy) : AbstractNode(copy) {
    }


    BvnorNode::~BvnorNode() {
    }


    void BvnorNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvnorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~(this->childs[0]->evaluate() | this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvnorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnot */


    BvnotNode::BvnotNode(AbstractNode* expr) {
      this->kind = BVNOT_NODE;
      this->addChild(expr);
      this->init();
    }


    BvnotNode::BvnotNode(const BvnotNode& copy) : AbstractNode(copy) {
    }


    BvnotNode::~BvnotNode() {
    }


    void BvnotNode::init(void) {
      if (this->childs.size() < 1)
        throw triton::exceptions::Ast("BvnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~this->childs[0]->evaluate() & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvnotNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvor */


    BvorNode::BvorNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvorNode::BvorNode(const BvorNode& copy) : AbstractNode(copy) {
    }


    BvorNode::~BvorNode() {
    }


    void BvorNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[0]->getBitvectorSize())
        throw triton::exceptions::Ast("BvorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() | this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvrol */


    BvrolNode::BvrolNode(triton::uint32 rot, AbstractNode* expr) {
      this->kind = BVROL_NODE;
      this->addChild(triton::ast::decimal(rot));
      this->addChild(expr);
      this->init();
    }


    BvrolNode::BvrolNode(AbstractNode* rot, AbstractNode* expr) {
      this->kind = BVROL_NODE;
      this->addChild(rot);
      this->addChild(expr);
      this->init();
    }


    BvrolNode::BvrolNode(const BvrolNode& copy) : AbstractNode(copy) {
    }



    BvrolNode::~BvrolNode() {
    }


    void BvrolNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvrolNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvrolNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      value = this->childs[1]->evaluate();

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value << rot) | (value >> (this->size - rot))) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvrolNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvrolNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvror */


    BvrorNode::BvrorNode(triton::uint32 rot, AbstractNode* expr) {
      this->kind = BVROR_NODE;
      this->addChild(triton::ast::decimal(rot));
      this->addChild(expr);
      this->init();
    }


    BvrorNode::BvrorNode(AbstractNode* rot, AbstractNode* expr) {
      this->kind = BVROR_NODE;
      this->addChild(rot);
      this->addChild(expr);
      this->init();
    }


    BvrorNode::BvrorNode(const BvrorNode& copy) : AbstractNode(copy) {
    }


    BvrorNode::~BvrorNode() {
    }


    void BvrorNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvrorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvrorNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      value = this->childs[1]->evaluate();

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value >> rot) | (value << (this->size - rot))) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvrorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvrorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsdiv */


    BvsdivNode::BvsdivNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSDIV_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsdivNode::BvsdivNode(const BvsdivNode& copy) : AbstractNode(copy) {
    }


    BvsdivNode::~BvsdivNode() {
    }


    void BvsdivNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (op2Signed == 0) {
        this->eval = (op1Signed < 0 ? 1 : -1);
        this->eval &= this->getBitvectorMask();
      }
      else
        this->eval = ((op1Signed / op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsdivNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsdivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsge */


    BvsgeNode::BvsgeNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSGE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsgeNode::BvsgeNode(const BvsgeNode& copy) : AbstractNode(copy) {
    }


    BvsgeNode::~BvsgeNode() {
    }


    void BvsgeNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed >= op2Signed);

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsgeNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsgeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsgt */


    BvsgtNode::BvsgtNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSGT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsgtNode::BvsgtNode(const BvsgtNode& copy) : AbstractNode(copy) {
    }


    BvsgtNode::~BvsgtNode() {
    }


    void BvsgtNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed > op2Signed);

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsgtNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsgtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvshl */


    BvshlNode::BvshlNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSHL_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvshlNode::BvshlNode(const BvshlNode& copy) : AbstractNode(copy) {
    }


    BvshlNode::~BvshlNode() {
    }


    void BvshlNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvshlNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvshlNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() << this->childs[1]->evaluate().convert_to<triton::uint32>()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvshlNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvshlNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsle */


    BvsleNode::BvsleNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSLE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsleNode::BvsleNode(const BvsleNode& copy) : AbstractNode(copy) {
    }


    BvsleNode::~BvsleNode() {
    }


    void BvsleNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsleNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsleNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed <= op2Signed);

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsleNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvslt */


    BvsltNode::BvsltNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSLT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsltNode::BvsltNode(const BvsltNode& copy) : AbstractNode(copy) {
    }


    BvsltNode::~BvsltNode() {
    }


    void BvsltNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsltNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsltNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed < op2Signed);

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsltNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsltNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsmod - 2's complement signed remainder (sign follows divisor) */


    BvsmodNode::BvsmodNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSMOD_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsmodNode::BvsmodNode(const BvsmodNode& copy) : AbstractNode(copy) {
    }


    BvsmodNode::~BvsmodNode() {
    }


    void BvsmodNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = this->childs[0]->evaluate();
      else
        this->eval = ((((op1Signed % op2Signed) + op2Signed) % op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsmodNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsmodNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsrem - 2's complement signed remainder (sign follows dividend) */


    BvsremNode::BvsremNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSREM_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsremNode::BvsremNode(const BvsremNode& copy) : AbstractNode(copy) {
    }


    BvsremNode::~BvsremNode() {
    }


    void BvsremNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsremNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsremNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = this->childs[0]->evaluate();
      else
        this->eval = ((op1Signed - ((op1Signed / op2Signed) * op2Signed)).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsremNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsub */


    BvsubNode::BvsubNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSUB_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvsubNode::BvsubNode(const BvsubNode& copy) : AbstractNode(copy) {
    }


    BvsubNode::~BvsubNode() {
    }


    void BvsubNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvsubNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsubNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() - this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvsubNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsubNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvudiv */


    BvudivNode::BvudivNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVUDIV_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvudivNode::BvudivNode(const BvudivNode& copy) : AbstractNode(copy) {
    }


    BvudivNode::~BvudivNode() {
    }


    void BvudivNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvudivNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvudivNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = (-1 & this->getBitvectorMask());
      else
        this->eval = (this->childs[0]->evaluate() / this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvudivNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvudivNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvuge */


    BvugeNode::BvugeNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVUGE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvugeNode::BvugeNode(const BvugeNode& copy) : AbstractNode(copy) {
    }


    BvugeNode::~BvugeNode() {
    }


    void BvugeNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvugeNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvugeNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() >= this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvugeNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvugeNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvugt */


    BvugtNode::BvugtNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVUGT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvugtNode::BvugtNode(const BvugtNode& copy) : AbstractNode(copy) {
    }


    BvugtNode::~BvugtNode() {
    }


    void BvugtNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvugtNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvugtNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() > this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvugtNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvugtNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvule */


    BvuleNode::BvuleNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVULE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvuleNode::BvuleNode(const BvuleNode& copy) : AbstractNode(copy) {
    }


    BvuleNode::~BvuleNode() {
    }


    void BvuleNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvuleNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvuleNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() <= this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvuleNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvuleNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvult */


    BvultNode::BvultNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVULT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvultNode::BvultNode(const BvultNode& copy) : AbstractNode(copy) {
    }


    BvultNode::~BvultNode() {
    }


    void BvultNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvultNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvultNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() < this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvultNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvultNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvurem */


    BvuremNode::BvuremNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVUREM_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvuremNode::BvuremNode(const BvuremNode& copy) : AbstractNode(copy) {
    }


    BvuremNode::~BvuremNode() {
    }


    void BvuremNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvuremNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvuremNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = this->childs[0]->evaluate();
      else
        this->eval = (this->childs[0]->evaluate() % this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvuremNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvuremNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxnor */


    BvxnorNode::BvxnorNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVXNOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvxnorNode::BvxnorNode(const BvxnorNode& copy) : AbstractNode(copy) {
    }


    BvxnorNode::~BvxnorNode() {
    }


    void BvxnorNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvxnorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvxnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~(this->childs[0]->evaluate() ^ this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvxnorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvxnorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxor */


    BvxorNode::BvxorNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVXOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    BvxorNode::BvxorNode(const BvxorNode& copy) : AbstractNode(copy) {
    }


    BvxorNode::~BvxorNode() {
    }


    void BvxorNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvxorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvxorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() ^ this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvxorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvxorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bv */


    BvNode::BvNode(triton::uint512 value, triton::uint32 size) {
      this->kind = BV_NODE;
      this->addChild(triton::ast::decimal(value));
      this->addChild(triton::ast::decimal(size));
      this->init();
    }


    BvNode::BvNode(const BvNode& copy) : AbstractNode(copy) {
    }


    BvNode::~BvNode() {
    }


    void BvNode::init(void) {
      triton::uint512 value = 0;
      triton::uint32 size   = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("BvNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE || this->childs[1]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("BvNode::init(): Size and value must be a DECIMAL_NODE.");

      value = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue();
      size  = reinterpret_cast<DecimalNode*>(this->childs[1])->getValue().convert_to<triton::uint32>();

      if (!size)
        throw triton::exceptions::Ast("BvNode::init(): Size connot be equal to zero.");

      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("BvNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      /* Init attributes */
      this->size = size;
      this->eval = (value & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void BvNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== compound */


    CompoundNode::CompoundNode(std::vector<AbstractNode*> exprs) {
      this->kind = COMPOUND_NODE;
      for (triton::uint32 index = 0; index < exprs.size(); index++)
        this->addChild(exprs[index]);
      this->init();
    }


    CompoundNode::CompoundNode(const CompoundNode& copy) : AbstractNode(copy) {
    }


    CompoundNode::~CompoundNode() {
    }


    void CompoundNode::init(void) {
      if (this->childs.size() < 1)
        throw triton::exceptions::Ast("CompoundNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 0;
      this->eval = 0;

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void CompoundNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 CompoundNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== concat */


    ConcatNode::ConcatNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = CONCAT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    ConcatNode::ConcatNode(std::vector<AbstractNode*> exprs) {
      this->kind = CONCAT_NODE;
      for (triton::uint32 index = 0; index < exprs.size(); index++)
        this->addChild(exprs[index]);
      this->init();
    }


    ConcatNode::ConcatNode(std::list<AbstractNode*> exprs) {
      this->kind = CONCAT_NODE;
      for (std::list<AbstractNode *>::iterator it = exprs.begin() ; it != exprs.end(); it++)
        this->addChild(*it);
      this->init();
    }


    ConcatNode::ConcatNode(const ConcatNode& copy) : AbstractNode(copy) {
    }


    ConcatNode::~ConcatNode() {
    }


    void ConcatNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("ConcatNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 0;
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->size += this->childs[index]->getBitvectorSize();
      }

      if (this->size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("ConcatNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = this->childs[0]->evaluate();
      for (triton::uint32 index = 0; index < this->childs.size()-1; index++)
        this->eval = ((this->eval << this->childs[index+1]->getBitvectorSize()) | this->childs[index+1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void ConcatNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ConcatNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Decimal node */


    DecimalNode::DecimalNode(triton::uint512 value) {
      this->kind  = DECIMAL_NODE;
      this->value = value;
      this->init();
    }


    DecimalNode::DecimalNode(const DecimalNode& copy) : AbstractNode(copy) {
      this->value = copy.value;
    }


    DecimalNode::~DecimalNode() {
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


    void DecimalNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 DecimalNode::hash(triton::uint32 deep) const {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== Declare node */


    DeclareFunctionNode::DeclareFunctionNode(std::string name, AbstractNode* bvDecl) {
      this->kind = DECLARE_FUNCTION_NODE;
      this->addChild(triton::ast::string(name));
      this->addChild(bvDecl);
      this->init();
    }


    DeclareFunctionNode::DeclareFunctionNode(const DeclareFunctionNode& copy) : AbstractNode(copy) {
    }


    DeclareFunctionNode::~DeclareFunctionNode() {
    }


    void DeclareFunctionNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("DeclareFunctionNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != STRING_NODE)
        throw triton::exceptions::Ast("DeclareFunctionNode::init(): The first argument must be a STRING_NODE.");

      if (this->childs[1]->getKind() != BVDECL_NODE)
        throw triton::exceptions::Ast("DeclareFunctionNode::init(): The second argument must be a BVDECL_NODE.");

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      this->eval = this->childs[1]->evaluate();

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void DeclareFunctionNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 DeclareFunctionNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Distinct node */


    DistinctNode::DistinctNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = DISTINCT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    DistinctNode::DistinctNode(const DistinctNode& copy) : AbstractNode(copy) {
    }


    DistinctNode::~DistinctNode() {
    }


    void DistinctNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("DistinctNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() != this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void DistinctNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 DistinctNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== equal */


    EqualNode::EqualNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = EQUAL_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    EqualNode::EqualNode(const EqualNode& copy) : AbstractNode(copy) {
    }


    EqualNode::~EqualNode() {
    }


    void EqualNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("EqualNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() == this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void EqualNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 EqualNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== extract */


    ExtractNode::ExtractNode(triton::uint32 high, triton::uint32 low, AbstractNode* expr) {
      this->kind = EXTRACT_NODE;
      this->addChild(triton::ast::decimal(high));
      this->addChild(triton::ast::decimal(low));
      this->addChild(expr);
      this->init();
    }


    ExtractNode::ExtractNode(const ExtractNode& copy) : AbstractNode(copy) {
    }


    ExtractNode::~ExtractNode() {
    }


    void ExtractNode::init(void) {
      triton::uint32 high = 0;
      triton::uint32 low  = 0;

      if (this->childs.size() < 3)
        throw triton::exceptions::Ast("ExtractNode::init(): Must take at least three childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE || this->childs[1]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("ExtractNode::init(): The highest and lower bit must be a DECIMAL_NODE.");

      high = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      low  = reinterpret_cast<DecimalNode*>(this->childs[1])->getValue().convert_to<triton::uint32>();

      if (low > high)
        throw triton::exceptions::Ast("ExtractNode::init(): The high bit must be greater than the low bit.");

      /* Init attributes */
      this->size = ((high - low) + 1);
      this->eval = ((this->childs[2]->evaluate() >> low) & this->getBitvectorMask());

      if (this->size > this->childs[2]->getBitvectorSize() || high >= this->childs[2]->getBitvectorSize())
        throw triton::exceptions::Ast("ExtractNode::init(): The size of the extraction is higher than the child expression.");

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void ExtractNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ExtractNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== ite */


    IteNode::IteNode(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr) {
      this->kind = ITE_NODE;
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
      this->init();
    }


    IteNode::IteNode(const IteNode& copy) : AbstractNode(copy) {
    }


    IteNode::~IteNode() {
    }


    void IteNode::init(void) {
      if (this->childs.size() < 3)
        throw triton::exceptions::Ast("IteNode::init(): Must take at least three childs.");

      if (this->childs[1]->getBitvectorSize() != this->childs[2]->getBitvectorSize())
        throw triton::exceptions::Ast("IteNode::init(): Must take two nodes of same size as 'then' and 'else' branches.");

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      this->eval = this->childs[0]->evaluate() ? this->childs[1]->evaluate() : this->childs[2]->evaluate();

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void IteNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 IteNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Land */


    LandNode::LandNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = LAND_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    LandNode::LandNode(const LandNode& copy) : AbstractNode(copy) {
    }


    LandNode::~LandNode() {
    }


    void LandNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("LandNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() && this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void LandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LandNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Let */


    LetNode::LetNode(std::string alias, AbstractNode* expr2, AbstractNode* expr3) {
      this->kind = LET_NODE;
      this->addChild(triton::ast::string(alias));
      this->addChild(expr2);
      this->addChild(expr3);
      this->init();
    }


    LetNode::LetNode(const LetNode& copy) : AbstractNode(copy) {
    }


    LetNode::~LetNode() {
    }


    void LetNode::init(void) {
      if (this->childs.size() < 3)
        throw triton::exceptions::Ast("LetNode::init(): Must take at least three childs.");

      if (this->childs[0]->getKind() != STRING_NODE)
        throw triton::exceptions::Ast("LetNode::init(): The alias node must be a STRING_NODE.");

      /* Init attributes */
      this->size = this->childs[2]->getBitvectorSize();
      this->eval = this->childs[2]->evaluate();

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void LetNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LetNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lnot */


    LnotNode::LnotNode(AbstractNode* expr) {
      this->kind = LNOT_NODE;
      this->addChild(expr);
      this->init();
    }


    LnotNode::LnotNode(const LnotNode& copy) : AbstractNode(copy) {
    }


    LnotNode::~LnotNode() {
    }


    void LnotNode::init(void) {
      if (this->childs.size() < 1)
        throw triton::exceptions::Ast("LnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 1;
      this->eval = !(this->childs[0]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void LnotNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LnotNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lor */


    LorNode::LorNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = LOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
      this->init();
    }


    LorNode::LorNode(const LorNode& copy) : AbstractNode(copy) {
    }


    LorNode::~LorNode() {
    }


    void LorNode::init(void) {
      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("LorNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() || this->childs[1]->evaluate());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void LorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LorNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Reference node */


    ReferenceNode::ReferenceNode(triton::usize value) {
      this->kind  = REFERENCE_NODE;
      this->value = value;
      this->init();
    }


    ReferenceNode::ReferenceNode(const ReferenceNode& copy) : AbstractNode(copy) {
      this->value = copy.value;
    }


    ReferenceNode::~ReferenceNode() {
    }


    void ReferenceNode::init(void) {
      /* Init attributes */
      if (!triton::api.isSymbolicExpressionIdExists(this->value)) {
        this->eval        = 0;
        this->size        = 0;
        this->symbolized  = false;
      }
      else {
        this->eval        = triton::api.getAstFromId(this->value)->evaluate();
        this->size        = triton::api.getAstFromId(this->value)->getBitvectorSize();
        this->symbolized  = triton::api.getAstFromId(this->value)->isSymbolized();

        triton::api.getAstFromId(this->value)->setParent(this);
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    triton::usize ReferenceNode::getValue(void) {
      return this->value;
    }


    void ReferenceNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ReferenceNode::hash(triton::uint32 deep) const {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== String node */


    StringNode::StringNode(std::string value) {
      this->kind  = STRING_NODE;
      this->value = value;
      this->init();
    }


    StringNode::StringNode(const StringNode& copy) : AbstractNode(copy) {
      this->value = copy.value;
    }


    StringNode::~StringNode() {
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


    void StringNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 StringNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::const_iterator it = this->value.cbegin(); it != this->value.cend(); it++)
        h = h ^ triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== sx */


    SxNode::SxNode(triton::uint32 sizeExt, AbstractNode* expr) {
      this->kind = SX_NODE;
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
      this->init();
    }


    SxNode::SxNode(const SxNode& copy) : AbstractNode(copy) {
    }


    SxNode::~SxNode() {
    }


    void SxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("SxNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("SxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->childs[1]->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("SxNode::SxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = ((((this->childs[1]->evaluate() >> (this->childs[1]->getBitvectorSize()-1)) == 0) ? this->childs[1]->evaluate() : (this->childs[1]->evaluate() | ~(this->childs[1]->getBitvectorMask()))) & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void SxNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 SxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Variable node */


    VariableNode::VariableNode(triton::engines::symbolic::SymbolicVariable& symVar) {
      this->kind  = VARIABLE_NODE;
      this->value = symVar.getName();
      this->init();
    }


    VariableNode::VariableNode(const VariableNode& copy) : AbstractNode(copy) {
      this->value = copy.value;
    }


    VariableNode::~VariableNode() {
    }


    void VariableNode::init(void) {
      triton::engines::symbolic::SymbolicVariable* symVar = nullptr;

      symVar = triton::api.getSymbolicVariableFromName(this->value);
      if (symVar) {
        this->size        = symVar->getSize();
        this->eval        = (symVar->getConcreteValue() & this->getBitvectorMask());
        this->symbolized  = true;
      }
      else
        throw triton::exceptions::Ast("VariableNode::init(): Variable not found.");

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    std::string VariableNode::getValue(void) {
      return this->value;
    }


    void VariableNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 VariableNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::const_iterator it = this->value.cbegin(); it != this->value.cend(); it++)
        h = h ^ triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== zx */


    ZxNode::ZxNode(triton::uint32 sizeExt, AbstractNode* expr) {
      this->kind = ZX_NODE;
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
      this->init();
    }


    ZxNode::ZxNode(const ZxNode& copy) : AbstractNode(copy) {
    }


    ZxNode::~ZxNode() {
    }


    void ZxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->childs.size() < 2)
        throw triton::exceptions::Ast("ZxNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw triton::exceptions::Ast("ZxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->childs[1]->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw triton::exceptions::Ast("ZxNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = (this->childs[1]->evaluate() & this->getBitvectorMask());

      /* Init childs and spread information */
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->childs[index]->setParent(this);
        this->symbolized |= this->childs[index]->isSymbolized();
      }

      /* Init parents */
      for (std::set<AbstractNode*>::iterator it = this->parents.begin(); it != this->parents.end(); it++)
        (*it)->init();
    }


    void ZxNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ZxNode::hash(triton::uint32 deep) const {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
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

    static inline void checkNode(AbstractNode* node) {
      if (node == nullptr)
        throw triton::exceptions::Ast("Node builders - Not enough memory");
    }


    AbstractNode* assert_(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) AssertNode(expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bv(triton::uint512 value, triton::uint32 size) {
      AbstractNode* node = new(std::nothrow) BvNode(value, size);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvadd(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvaddNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvandNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvashr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvashrNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvdecl(triton::uint32 size) {
      AbstractNode* node = new(std::nothrow) BvdeclNode(size);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvfalse(void) {
      AbstractNode* node = new(std::nothrow) BvNode(0, 1);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvlshr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvlshrNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvmul(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvmulNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvnand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvnandNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvneg(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvnegNode(expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvnorNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvnot(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvnotNode(expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvorNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvrol(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrolNode(rot, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvrol(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrolNode(rot, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvror(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrorNode(rot, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvror(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) BvrorNode(rot, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsdiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsdivNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsgeNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsgt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsgtNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvshl(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvshlNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsle(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsleNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvslt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsltNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsmod(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsmodNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsrem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsremNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvsub(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvsubNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvtrue(void) {
      AbstractNode* node = new(std::nothrow) BvNode(1, 1);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvudiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvudivNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvuge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvugeNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvugt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvugtNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvule(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvuleNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvult(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvultNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvurem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvuremNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


     AbstractNode* bvxnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvxnorNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* bvxor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) BvxorNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* compound(std::vector<AbstractNode*> exprs) {
      AbstractNode* node = new(std::nothrow) CompoundNode(exprs);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* concat(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) ConcatNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* concat(std::vector<AbstractNode*> exprs) {
      AbstractNode* node = new(std::nothrow) ConcatNode(exprs);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* concat(std::list<AbstractNode*> exprs) {
      AbstractNode* node = new(std::nothrow) ConcatNode(exprs);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* decimal(triton::uint512 value) {
      AbstractNode* node = new(std::nothrow) DecimalNode(value);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* declareFunction(std::string name, AbstractNode* bvDecl) {
      AbstractNode* node = new(std::nothrow) DeclareFunctionNode(name, bvDecl);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* distinct(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) DistinctNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* equal(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) EqualNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) ExtractNode(high, low, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr) {
      AbstractNode* node = new(std::nothrow) IteNode(ifExpr, thenExpr, elseExpr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* land(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) LandNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* let(std::string alias, AbstractNode* expr2, AbstractNode* expr3) {
      AbstractNode* node = new(std::nothrow) LetNode(alias, expr2, expr3);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* lnot(AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) LnotNode(expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* lor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new(std::nothrow) LorNode(expr1, expr2);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* reference(triton::usize value) {
      AbstractNode* node = new(std::nothrow) ReferenceNode(value);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* string(std::string value) {
      AbstractNode* node = new(std::nothrow) StringNode(value);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* sx(triton::uint32 sizeExt, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) SxNode(sizeExt, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* variable(triton::engines::symbolic::SymbolicVariable& symVar) {
      AbstractNode* ret  = nullptr;
      AbstractNode* node = new(std::nothrow) VariableNode(symVar);

      triton::ast::checkNode(node);
      ret = triton::api.recordAstNode(node);
      triton::api.recordVariableAstNode(symVar.getName(), ret);

      return ret;
    }


    AbstractNode* zx(triton::uint32 sizeExt, AbstractNode* expr) {
      AbstractNode* node = new(std::nothrow) ZxNode(sizeExt, expr);
      triton::ast::checkNode(node);

      return triton::api.recordAstNode(node);
    }


    AbstractNode* newInstance(AbstractNode* node) {
      AbstractNode* newNode = nullptr;

      if (node == nullptr)
        return nullptr;

      switch (node->getKind()) {
        case ASSERT_NODE:               newNode = new(std::nothrow) AssertNode(*reinterpret_cast<AssertNode*>(node)); break;
        case BVADD_NODE:                newNode = new(std::nothrow) BvaddNode(*reinterpret_cast<BvaddNode*>(node)); break;
        case BVAND_NODE:                newNode = new(std::nothrow) BvandNode(*reinterpret_cast<BvandNode*>(node)); break;
        case BVASHR_NODE:               newNode = new(std::nothrow) BvashrNode(*reinterpret_cast<BvashrNode*>(node)); break;
        case BVDECL_NODE:               newNode = new(std::nothrow) BvdeclNode(*reinterpret_cast<BvdeclNode*>(node)); break;
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
        case COMPOUND_NODE:             newNode = new(std::nothrow) CompoundNode(*reinterpret_cast<CompoundNode*>(node)); break;
        case CONCAT_NODE:               newNode = new(std::nothrow) ConcatNode(*reinterpret_cast<ConcatNode*>(node)); break;
        case DECIMAL_NODE:              newNode = new(std::nothrow) DecimalNode(*reinterpret_cast<DecimalNode*>(node)); break;
        case DECLARE_FUNCTION_NODE:     newNode = new(std::nothrow) DeclareFunctionNode(*reinterpret_cast<DeclareFunctionNode*>(node)); break;
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

      return newNode;
    }

  }; /* ast namespace */
}; /* triton namespace */

