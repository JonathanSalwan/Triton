//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cmath>

#include <api.hpp>
#include <ast.hpp>
#include <tritonToZ3Ast.hpp>
#include <z3Result.hpp>



namespace triton {
  namespace ast {

    /* ====== Abstract node */

    AbstractNode::AbstractNode(enum kind_e kind) {
      this->kind    = kind;
      this->size    = 0;
      this->eval    = 0;
      this->parent  = nullptr;
    }


    AbstractNode::AbstractNode() {
      this->kind    = UNDEFINED_NODE;
      this->size    = 0;
      this->eval    = 0;
      this->parent  = nullptr;
    }


    AbstractNode::AbstractNode(const AbstractNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    AbstractNode::~AbstractNode() {
      /* virtual */
    }


    enum kind_e AbstractNode::getKind(void) {
      return this->kind;
    }


    triton::uint32 AbstractNode::getBitvectorSize(void) {
      return this->size;
    }


    triton::uint512 AbstractNode::getBitvectorMask(void) {
      triton::uint512 mask = -1;
      mask = mask >> (512 - this->size);
      return mask;
    }


    bool AbstractNode::isSigned(void) {
      if ((this->eval >> (this->size-1)) & 1)
        return true;
      return false;
    }


    triton::uint512 AbstractNode::evaluate(void) {
      return this->eval;
    }


    std::vector<AbstractNode*>& AbstractNode::getChilds(void) {
      return this->childs;
    }


    AbstractNode* AbstractNode::getParent(void) {
      return this->parent;
    }


    void AbstractNode::setParent(AbstractNode* p) {
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_SUMMARIES) == false)
        this->parent = p;
    }


    void AbstractNode::addChild(AbstractNode* child) {
      this->childs.push_back(child);
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


    AssertNode::AssertNode(const AssertNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    AssertNode::~AssertNode() {
    }


    void AssertNode::init(void) {
      if (this->childs.size() < 1)
        throw std::runtime_error("AssertNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 1;
      this->eval = 0;

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void AssertNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 AssertNode::hash(triton::uint32 deep) {
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


    BvaddNode::BvaddNode(const BvaddNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvaddNode::~BvaddNode() {
    }


    void BvaddNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvaddNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvaddNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() + this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvaddNode::accept(AstVisitor& v) {
       v(*this);
    }


    triton::uint512 BvaddNode::hash(triton::uint32 deep) {
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


    BvandNode::BvandNode(const BvandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvandNode::~BvandNode() {
    }


    void BvandNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvandNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() & this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvandNode::hash(triton::uint32 deep) {
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


    BvashrNode::BvashrNode(const BvashrNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvashrNode::~BvashrNode() {
    }


    void BvashrNode::init(void) {
      triton::uint32 shift  = 0;
      triton::uint512 mask  = 0;
      triton::uint512 value = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvashrNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvashrNode::init(): Must take two nodes of same size.");

      value = this->childs[0]->evaluate();
      shift = this->childs[1]->evaluate().convert_to<triton::uint32>();

      /* Mask based on the sign */
      if (this->childs[0]->isSigned())
        mask = (1 << (this->childs[0]->getBitvectorSize()-1));

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

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
        for (triton::uint32 index = 1; index <= shift; index++) {
          this->eval = (((this->eval >> 1) | mask) & this->getBitvectorMask());
        }
      }

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


   void BvashrNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvashrNode::hash(triton::uint32 deep) {
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


    BvdeclNode::BvdeclNode(const BvdeclNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvdeclNode::~BvdeclNode() {
    }


    void BvdeclNode::init(void) {
      triton::uint32 size = 0;

      if (this->childs.size() < 1)
        throw std::runtime_error("BvdeclNode::init(): Must take at least one child.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("BvdeclNode::init(): Child must be a DECIMAL_NODE.");

      size = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      if (!size)
        throw std::runtime_error("BvdeclNode::init(): Size connot be equal to zero.");

      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("BvdeclNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      /* Init attributes */
      this->size = size;
      this->eval = 0;

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvdeclNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvdeclNode::hash(triton::uint32 deep) {
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


    BvlshrNode::BvlshrNode(const BvlshrNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvlshrNode::~BvlshrNode() {
    }


    void BvlshrNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvlshrNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvlshrNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() >> this->childs[1]->evaluate().convert_to<triton::uint32>());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvlshrNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvlshrNode::hash(triton::uint32 deep) {
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


    BvmulNode::BvmulNode(const BvmulNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvmulNode::~BvmulNode() {
    }


    void BvmulNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvmulNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvmulNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() * this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvmulNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvmulNode::hash(triton::uint32 deep) {
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


    BvnandNode::BvnandNode(const BvnandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvnandNode::~BvnandNode() {
    }


    void BvnandNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvnandNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvnandNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~(this->childs[0]->evaluate() & this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvnandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnandNode::hash(triton::uint32 deep) {
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


    BvnegNode::BvnegNode(const BvnegNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvnegNode::~BvnegNode() {
    }


    void BvnegNode::init(void) {
      if (this->childs.size() < 1)
        throw std::runtime_error("BvnegNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((-(this->childs[0]->evaluate().convert_to<triton::sint512>())).convert_to<triton::uint512>() & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvnegNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnegNode::hash(triton::uint32 deep) {
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


    BvnorNode::BvnorNode(const BvnorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvnorNode::~BvnorNode() {
    }


    void BvnorNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvnorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~(this->childs[0]->evaluate() | this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvnorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnorNode::hash(triton::uint32 deep) {
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


    BvnotNode::BvnotNode(const BvnotNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvnotNode::~BvnotNode() {
    }


    void BvnotNode::init(void) {
      if (this->childs.size() < 1)
        throw std::runtime_error("BvnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~this->childs[0]->evaluate() & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvnotNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvnotNode::hash(triton::uint32 deep) {
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


    BvorNode::BvorNode(const BvorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvorNode::~BvorNode() {
    }


    void BvorNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[0]->getBitvectorSize())
        throw std::runtime_error("BvorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() | this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvorNode::hash(triton::uint32 deep) {
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


    BvrolNode::BvrolNode(const BvrolNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }



    BvrolNode::~BvrolNode() {
    }


    void BvrolNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvrolNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("BvrolNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      value = this->childs[1]->evaluate();

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value << rot) | (value >> (this->size - rot))) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvrolNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvrolNode::hash(triton::uint32 deep) {
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


    BvrorNode::BvrorNode(const BvrorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvrorNode::~BvrorNode() {
    }


    void BvrorNode::init(void) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvrorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("BvrorNode::init(): rot must be a DECIMAL_NODE.");

      rot   = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      value = this->childs[1]->evaluate();

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      rot %= this->size;
      this->eval = (((value >> rot) | (value << (this->size - rot))) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvrorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvrorNode::hash(triton::uint32 deep) {
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


    BvsdivNode::BvsdivNode(const BvsdivNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsdivNode::~BvsdivNode() {
    }


    void BvsdivNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsdivNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsdivNode::init(): Must take two nodes of same size.");

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

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsdivNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsdivNode::hash(triton::uint32 deep) {
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


    BvsgeNode::BvsgeNode(const BvsgeNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsgeNode::~BvsgeNode() {
    }


    void BvsgeNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsgeNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsgeNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed >= op2Signed);

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsgeNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsgeNode::hash(triton::uint32 deep) {
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


    BvsgtNode::BvsgtNode(const BvsgtNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsgtNode::~BvsgtNode() {
    }


    void BvsgtNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsgtNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsgtNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed > op2Signed);

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsgtNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsgtNode::hash(triton::uint32 deep) {
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


    BvshlNode::BvshlNode(const BvshlNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvshlNode::~BvshlNode() {
    }


    void BvshlNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvshlNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvshlNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() << this->childs[1]->evaluate().convert_to<triton::uint32>()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvshlNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvshlNode::hash(triton::uint32 deep) {
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


    BvsleNode::BvsleNode(const BvsleNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsleNode::~BvsleNode() {
    }


    void BvsleNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsleNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsleNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed <= op2Signed);

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsleNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsleNode::hash(triton::uint32 deep) {
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


    BvsltNode::BvsltNode(const BvsltNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsltNode::~BvsltNode() {
    }


    void BvsltNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsltNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsltNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = 1;
      this->eval = (op1Signed < op2Signed);

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsltNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsltNode::hash(triton::uint32 deep) {
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


    BvsmodNode::BvsmodNode(const BvsmodNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsmodNode::~BvsmodNode() {
    }


    void BvsmodNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsmodNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsmodNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = this->childs[0]->evaluate();
      else {
        if (op2Signed < 0)
          this->eval = ((op1Signed % op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());
        else
          this->eval = ((this->childs[0]->evaluate() % this->childs[1]->evaluate()) & this->getBitvectorMask());
      }

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsmodNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsmodNode::hash(triton::uint32 deep) {
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


    BvsremNode::BvsremNode(const BvsremNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsremNode::~BvsremNode() {
    }


    void BvsremNode::init(void) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvsremNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsremNode::init(): Must take two nodes of same size.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->childs[0]);
      op2Signed = triton::ast::modularSignExtend(this->childs[1]);

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = this->childs[0]->evaluate();
      else {
        if (op1Signed < 0)
          this->eval = ((op1Signed % op2Signed).convert_to<triton::uint512>() & this->getBitvectorMask());
        else
          this->eval = ((this->childs[0]->evaluate() % this->childs[1]->evaluate()) & this->getBitvectorMask());
      }

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsremNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsremNode::hash(triton::uint32 deep) {
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


    BvsubNode::BvsubNode(const BvsubNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvsubNode::~BvsubNode() {
    }


    void BvsubNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvsubNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvsubNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = ((this->childs[0]->evaluate() - this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvsubNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvsubNode::hash(triton::uint32 deep) {
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


    BvudivNode::BvudivNode(const BvudivNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvudivNode::~BvudivNode() {
    }


    void BvudivNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvudivNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvudivNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = (-1 & this->getBitvectorMask());
      else
        this->eval = (this->childs[0]->evaluate() / this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvudivNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvudivNode::hash(triton::uint32 deep) {
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


    BvugeNode::BvugeNode(const BvugeNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvugeNode::~BvugeNode() {
    }


    void BvugeNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvugeNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvugeNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() >= this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvugeNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvugeNode::hash(triton::uint32 deep) {
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


    BvugtNode::BvugtNode(const BvugtNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvugtNode::~BvugtNode() {
    }


    void BvugtNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvugtNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvugtNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() > this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvugtNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvugtNode::hash(triton::uint32 deep) {
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


    BvuleNode::BvuleNode(const BvuleNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvuleNode::~BvuleNode() {
    }


    void BvuleNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvuleNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvuleNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() <= this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvuleNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvuleNode::hash(triton::uint32 deep) {
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


    BvultNode::BvultNode(const BvultNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvultNode::~BvultNode() {
    }


    void BvultNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvultNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvultNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() < this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvultNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvultNode::hash(triton::uint32 deep) {
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


    BvuremNode::BvuremNode(const BvuremNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvuremNode::~BvuremNode() {
    }


    void BvuremNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvuremNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvuremNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();

      if (this->childs[1]->evaluate() == 0)
        this->eval = this->childs[0]->evaluate();
      else
        this->eval = (this->childs[0]->evaluate() % this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvuremNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvuremNode::hash(triton::uint32 deep) {
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


    BvxnorNode::BvxnorNode(const BvxnorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvxnorNode::~BvxnorNode() {
    }


    void BvxnorNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvxnorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvxnorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (~(this->childs[0]->evaluate() ^ this->childs[1]->evaluate()) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvxnorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvxnorNode::hash(triton::uint32 deep) {
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


    BvxorNode::BvxorNode(const BvxorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvxorNode::~BvxorNode() {
    }


    void BvxorNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("BvxorNode::init(): Must take at least two childs.");

      if (this->childs[0]->getBitvectorSize() != this->childs[1]->getBitvectorSize())
        throw std::runtime_error("BvxorNode::init(): Must take two nodes of same size.");

      /* Init attributes */
      this->size = this->childs[0]->getBitvectorSize();
      this->eval = (this->childs[0]->evaluate() ^ this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvxorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvxorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bv */


    BvNode::BvNode(triton::uint128 value, triton::uint32 size) {
      this->kind = BV_NODE;
      this->addChild(triton::ast::decimal(value));
      this->addChild(triton::ast::decimal(size));
      this->init();
    }


    BvNode::BvNode(const BvNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    BvNode::~BvNode() {
    }


    void BvNode::init(void) {
      triton::uint128 value = 0;
      triton::uint32 size   = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("BvNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE || this->childs[1]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("BvNode::init(): Size and value must be a DECIMAL_NODE.");

      value = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue();
      size  = reinterpret_cast<DecimalNode*>(this->childs[1])->getValue().convert_to<triton::uint32>();

      if (!size)
        throw std::runtime_error("BvNode::init(): Size connot be equal to zero.");

      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("BvNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      /* Init attributes */
      this->size = size;
      this->eval = (value & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void BvNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 BvNode::hash(triton::uint32 deep) {
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


    CompoundNode::CompoundNode(const CompoundNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    CompoundNode::~CompoundNode() {
    }


    void CompoundNode::init(void) {
      if (this->childs.size() < 1)
        throw std::runtime_error("CompoundNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size = 0;
      this->eval = 0;

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void CompoundNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 CompoundNode::hash(triton::uint32 deep) {
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


    ConcatNode::ConcatNode(const ConcatNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    ConcatNode::~ConcatNode() {
    }


    void ConcatNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("ConcatNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 0;
      for (triton::uint32 index = 0; index < this->childs.size(); index++) {
        this->size += this->childs[index]->getBitvectorSize();
      }

      if (this->size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("ConcatNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = this->childs[0]->evaluate();
      for (triton::uint32 index = 0; index < this->childs.size()-1; index++)
        this->eval = ((this->eval << this->childs[index+1]->getBitvectorSize()) | this->childs[index+1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void ConcatNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ConcatNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Decimal node */


    DecimalNode::DecimalNode(triton::uint128 value) {
      this->kind  = DECIMAL_NODE;
      this->value = value;
      this->init();
    }


    DecimalNode::DecimalNode(const DecimalNode& copy) {
      this->kind   = copy.kind;
      this->value  = copy.value;
      this->size   = copy.size;
      this->eval   = copy.eval;
      this->parent = copy.parent;
    }


    DecimalNode::~DecimalNode() {
    }


    void DecimalNode::init(void) {
      /* Init attributes */
      this->size = 0;
      this->eval = 0;

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    triton::uint128 DecimalNode::getValue(void) {
      return this->value;
    }


    void DecimalNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 DecimalNode::hash(triton::uint32 deep) {
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


    DeclareFunctionNode::DeclareFunctionNode(const DeclareFunctionNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    DeclareFunctionNode::~DeclareFunctionNode() {
    }


    void DeclareFunctionNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("DeclareFunctionNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != STRING_NODE)
        throw std::runtime_error("DeclareFunctionNode::init(): The first argument must be a STRING_NODE.");

      if (this->childs[1]->getKind() != BVDECL_NODE)
        throw std::runtime_error("DeclareFunctionNode::init(): The second argument must be a BVDECL_NODE.");

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      this->eval = this->childs[1]->evaluate();

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void DeclareFunctionNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 DeclareFunctionNode::hash(triton::uint32 deep) {
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


    DistinctNode::DistinctNode(const DistinctNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    DistinctNode::~DistinctNode() {
    }


    void DistinctNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("DistinctNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() != this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void DistinctNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 DistinctNode::hash(triton::uint32 deep) {
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


    EqualNode::EqualNode(const EqualNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    EqualNode::~EqualNode() {
    }


    void EqualNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("EqualNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() == this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void EqualNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 EqualNode::hash(triton::uint32 deep) {
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


    ExtractNode::ExtractNode(const ExtractNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    ExtractNode::~ExtractNode() {
    }


    void ExtractNode::init(void) {
      triton::uint32 high = 0;
      triton::uint32 low  = 0;

      if (this->childs.size() < 3)
        throw std::runtime_error("ExtractNode::init(): Must take at least three childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE || this->childs[1]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("ExtractNode::init(): The highest and lower bit must be a DECIMAL_NODE.");

      high = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();
      low  = reinterpret_cast<DecimalNode*>(this->childs[1])->getValue().convert_to<triton::uint32>();

      if (low > high)
        throw std::runtime_error("ExtractNode::init(): The high bit must be greater than the low bit.");

      /* Init attributes */
      this->size = ((high - low) + 1);
      this->eval = ((this->childs[2]->evaluate() >> low) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void ExtractNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ExtractNode::hash(triton::uint32 deep) {
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


    IteNode::IteNode(const IteNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    IteNode::~IteNode() {
    }


    void IteNode::init(void) {
      if (this->childs.size() < 3)
        throw std::runtime_error("IteNode::init(): Must take at least three childs.");

      if (this->childs[1]->getBitvectorSize() != this->childs[2]->getBitvectorSize())
        throw std::runtime_error("IteNode::init(): Must take two nodes of same size as 'then' and 'else' branches.");

      /* Init attributes */
      this->size = this->childs[1]->getBitvectorSize();
      this->eval = this->childs[0]->evaluate() ? this->childs[1]->evaluate() : this->childs[2]->evaluate();

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void IteNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 IteNode::hash(triton::uint32 deep) {
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


    LandNode::LandNode(const LandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    LandNode::~LandNode() {
    }


    void LandNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("LandNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() && this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void LandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LandNode::hash(triton::uint32 deep) {
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


    LetNode::LetNode(const LetNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    LetNode::~LetNode() {
    }


    void LetNode::init(void) {
      if (this->childs.size() < 3)
        throw std::runtime_error("LetNode::init(): Must take at least three childs.");

      if (this->childs[0]->getKind() != STRING_NODE)
        throw std::runtime_error("LetNode::init(): The alias node must be a STRING_NODE.");

      /* Init attributes */
      this->size = this->childs[2]->getBitvectorSize();
      this->eval = this->childs[2]->evaluate();

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void LetNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LetNode::hash(triton::uint32 deep) {
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


    LnotNode::LnotNode(const LnotNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    LnotNode::~LnotNode() {
    }


    void LnotNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("LnotNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = !(this->childs[0]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void LnotNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LnotNode::hash(triton::uint32 deep) {
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


    LorNode::LorNode(const LorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    LorNode::~LorNode() {
    }


    void LorNode::init(void) {
      if (this->childs.size() < 2)
        throw std::runtime_error("LorNode::init(): Must take at least two childs.");

      /* Init attributes */
      this->size = 1;
      this->eval = (this->childs[0]->evaluate() || this->childs[1]->evaluate());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void LorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 LorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Reference node */


    ReferenceNode::ReferenceNode(triton::__uint value) {
      this->kind  = REFERENCE_NODE;
      this->value = value;
      this->init();
    }


    ReferenceNode::ReferenceNode(const ReferenceNode& copy) {
      this->kind   = copy.kind;
      this->value  = copy.value;
      this->size   = copy.size;
      this->eval   = copy.eval;
      this->parent = copy.parent;
    }


    ReferenceNode::~ReferenceNode() {
    }


    void ReferenceNode::init(void) {
      /* Init attributes */
      if (!triton::api.isSymbolicExpressionIdExists(this->value)) {
        this->size = 0;
        this->eval = 0;
      }
      else {
        this->size = triton::api.getAstFromId(this->value)->getBitvectorSize();
        this->eval = triton::api.getAstFromId(this->value)->evaluate();
      }

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    triton::__uint ReferenceNode::getValue(void) {
      return this->value;
    }


    void ReferenceNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ReferenceNode::hash(triton::uint32 deep) {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== String node */


    StringNode::StringNode(std::string value) {
      this->kind  = STRING_NODE;
      this->value = value;
    }


    StringNode::StringNode(const StringNode& copy) {
      this->kind   = copy.kind;
      this->value  = copy.value;
      this->size   = copy.size;
      this->eval   = copy.eval;
      this->parent = copy.parent;
    }


    StringNode::~StringNode() {
    }


    void StringNode::init(void) {
      /* Init attributes */
      this->size  = 0;
      this->eval  = 0;

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    std::string StringNode::getValue(void) {
      return this->value;
    }


    void StringNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 StringNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::iterator it=this->value.begin(); it != this->value.end(); it++)
        h = h * triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== sx */


    SxNode::SxNode(triton::uint32 sizeExt, AbstractNode* expr) {
      this->kind = SX_NODE;
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
      this->init();
    }


    SxNode::SxNode(const SxNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    SxNode::~SxNode() {
    }


    void SxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("SxNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("SxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->childs[1]->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("SxNode::SxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = ((((this->childs[1]->evaluate() >> (this->childs[1]->getBitvectorSize()-1)) == 0) ? this->childs[1]->evaluate() : (this->childs[1]->evaluate() | ~(this->childs[1]->getBitvectorMask()))) & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void SxNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 SxNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Variable node */


    VariableNode::VariableNode(triton::engines::symbolic::SymbolicVariable& symVar) {
      this->kind  = VARIABLE_NODE;
      this->value = symVar.getSymVarName();
      this->size  = symVar.getSymVarSize();
      this->eval  = (symVar.getConcreteValue() & this->getBitvectorMask());
    }


    VariableNode::VariableNode(const VariableNode& copy) {
      this->kind   = copy.kind;
      this->value  = copy.value;
      this->size   = copy.size;
      this->eval   = copy.eval;
      this->parent = copy.parent;
    }


    VariableNode::~VariableNode() {
    }


    void VariableNode::init(void) {
      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    std::string VariableNode::getValue(void) {
      return this->value;
    }


    void VariableNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 VariableNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::iterator it=this->value.begin(); it != this->value.end(); it++)
        h = h * triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== zx */


    ZxNode::ZxNode(triton::uint32 sizeExt, AbstractNode* expr) {
      this->kind = ZX_NODE;
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
      this->init();
    }


    ZxNode::ZxNode(const ZxNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      this->eval = copy.eval;
      this->parent = copy.parent;

      /* Copy and init childs */
      for (triton::uint32 index = 0; index < copy.childs.size(); index++) {
        this->childs.push_back(copy.childs[index]);
        copy.childs[index]->setParent(this);
      }
    }


    ZxNode::~ZxNode() {
    }


    void ZxNode::init(void) {
      triton::uint32 sizeExt = 0;

      if (this->childs.size() < 2)
        throw std::runtime_error("ZxNode::init(): Must take at least two childs.");

      if (this->childs[0]->getKind() != DECIMAL_NODE)
        throw std::runtime_error("ZxNode::init(): The sizeExt must be a DECIMAL_NODE.");

      sizeExt = reinterpret_cast<DecimalNode*>(this->childs[0])->getValue().convert_to<triton::uint32>();

      /* Init attributes */
      this->size = sizeExt + this->childs[1]->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("ZxNode::init(): Size connot be greater than MAX_BITS_SUPPORTED.");

      this->eval = (this->childs[1]->evaluate() & this->getBitvectorMask());

      /* Init childs */
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        this->childs[index]->setParent(this);

      /* Init parents */
      if (this->parent)
        this->parent->init();
    }


    void ZxNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 ZxNode::hash(triton::uint32 deep) {
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
      return triton::api.printAstRepresentation(stream, node);
    }


    /* Compares two trees */
    bool operator==(AbstractNode& node1, AbstractNode& node2) {
      return node1.hash(1) == node2.hash(1);
    }


  }; /* ast namespace */
}; /* triton namespace */



/* ====== Garbage collector utils */

namespace triton {
  namespace ast {

    /* Global container. This container contains all allocated nodes. */
    std::set<AbstractNode*> allocatedNodes;


    /* Go through every allocated nodes and free them */
    void freeAllAstNodes(void) {
      std::set<AbstractNode*>::const_iterator it;
      for (it = triton::ast::allocatedNodes.begin(); it != triton::ast::allocatedNodes.end(); it++) {
        (*it)->getChilds().clear();
        delete *it;
      }
      triton::ast::allocatedNodes.clear();
    }


    /* Frees a set of nodes and removes them from the global container. */
    void freeAstNodes(std::set<AbstractNode*>& nodes) {
      std::set<AbstractNode*>::iterator it;
      for (it = nodes.begin(); it != nodes.end(); it++) {
        triton::ast::allocatedNodes.erase(*it);
        delete *it;
      }
      nodes.clear();
    }


    /* Extracts all unique nodes from a partial AST into the uniqueNodes set */
    void extractUniqueAstNodes(std::set<AbstractNode*>& uniqueNodes, AbstractNode* root) {
      std::vector<AbstractNode*>::const_iterator it;
      uniqueNodes.insert(root);
      for (it = root->getChilds().begin(); it != root->getChilds().end(); it++)
        triton::ast::extractUniqueAstNodes(uniqueNodes, *it);
    }


    /* Records the allocated node or returns the same node if it already exists inside the summaries. */
    AbstractNode* recordNode(AbstractNode* node) {
      /* Check if the AST_SUMMARIES is enabled. */
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_SUMMARIES)) {
        AbstractNode* ret = triton::api.browseAstSummaries(node);
        if (ret != nullptr)
          return ret;
      }
      else {
        /* Record the node */
        triton::ast::allocatedNodes.insert(node);
      }
      return node;
    }


    triton::uint512 pow(triton::uint512 hash, triton::uint32 n) {
      for (triton::uint32 i = 0; i < n; i++)
        hash = hash * hash;
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

    AbstractNode* assert_(AbstractNode* expr) {
      AbstractNode* node = new AssertNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bv(triton::uint128 value, triton::uint32 size) {
      AbstractNode* node = new BvNode(value, size);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvadd(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvaddNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvashr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvashrNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvdecl(triton::uint32 size) {
      AbstractNode* node = new BvdeclNode(size);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvfalse(void) {
      AbstractNode* node = new BvNode(0, 1);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvlshr(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvlshrNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvmul(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvmulNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvnand(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvnandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvneg(AbstractNode* expr) {
      AbstractNode* node = new BvnegNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvnorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvnot(AbstractNode* expr) {
      AbstractNode* node = new BvnotNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvrol(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new BvrolNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvrol(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new BvrolNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvror(triton::uint32 rot, AbstractNode* expr) {
      AbstractNode* node = new BvrorNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvror(AbstractNode* rot, AbstractNode* expr) {
      AbstractNode* node = new BvrorNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsdiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsdivNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsgeNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsgt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsgtNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvshl(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvshlNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsle(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsleNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvslt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsltNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsmod(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsmodNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsrem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsremNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvsub(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvsubNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvtrue(void) {
      AbstractNode* node = new BvNode(1, 1);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvudiv(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvudivNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvuge(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvugeNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvugt(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvugtNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvule(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvuleNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvult(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvultNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvurem(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvuremNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


     AbstractNode* bvxnor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvxnorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* bvxor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new BvxorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* compound(std::vector<AbstractNode*> exprs) {
      AbstractNode* node = new CompoundNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* concat(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new ConcatNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* concat(std::vector<AbstractNode*> exprs) {
      AbstractNode* node = new ConcatNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* concat(std::list<AbstractNode*> exprs) {
      AbstractNode* node = new ConcatNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* decimal(triton::uint128 value) {
      AbstractNode* node = new DecimalNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* declareFunction(std::string name, AbstractNode* bvDecl) {
      AbstractNode* node = new DeclareFunctionNode(name, bvDecl);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* distinct(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new DistinctNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* equal(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new EqualNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr) {
      AbstractNode* node = new ExtractNode(high, low, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr) {
      AbstractNode* node = new IteNode(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* land(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new LandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* let(std::string alias, AbstractNode* expr2, AbstractNode* expr3) {
      AbstractNode* node = new LetNode(alias, expr2, expr3);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* lnot(AbstractNode* expr) {
      AbstractNode* node = new LnotNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* lor(AbstractNode* expr1, AbstractNode* expr2) {
      AbstractNode* node = new LorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* reference(triton::__uint value) {
      AbstractNode* node = new ReferenceNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* string(std::string value) {
      AbstractNode* node = new StringNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* sx(triton::uint32 sizeExt, AbstractNode* expr) {
      AbstractNode* node = new SxNode(sizeExt, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* variable(triton::engines::symbolic::SymbolicVariable& symVar) {
      AbstractNode* node = new VariableNode(symVar);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* zx(triton::uint32 sizeExt, AbstractNode* expr) {
      AbstractNode* node = new ZxNode(sizeExt, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    AbstractNode* newInstance(AbstractNode* node) {
      AbstractNode* newNode = nullptr;
      switch (node->getKind()) {
        case ASSERT_NODE:               newNode = new AssertNode(*reinterpret_cast<AssertNode*>(node)); break;
        case BVADD_NODE:                newNode = new BvaddNode(*reinterpret_cast<BvaddNode*>(node)); break;
        case BVAND_NODE:                newNode = new BvandNode(*reinterpret_cast<BvandNode*>(node)); break;
        case BVASHR_NODE:               newNode = new BvashrNode(*reinterpret_cast<BvashrNode*>(node)); break;
        case BVDECL_NODE:               newNode = new BvdeclNode(*reinterpret_cast<BvdeclNode*>(node)); break;
        case BVLSHR_NODE:               newNode = new BvlshrNode(*reinterpret_cast<BvlshrNode*>(node)); break;
        case BVMUL_NODE:                newNode = new BvmulNode(*reinterpret_cast<BvmulNode*>(node)); break;
        case BVNAND_NODE:               newNode = new BvnandNode(*reinterpret_cast<BvnandNode*>(node)); break;
        case BVNEG_NODE:                newNode = new BvnegNode(*reinterpret_cast<BvnegNode*>(node)); break;
        case BVNOR_NODE:                newNode = new BvnorNode(*reinterpret_cast<BvnorNode*>(node)); break;
        case BVNOT_NODE:                newNode = new BvnotNode(*reinterpret_cast<BvnotNode*>(node)); break;
        case BVOR_NODE:                 newNode = new BvorNode(*reinterpret_cast<BvorNode*>(node)); break;
        case BVROL_NODE:                newNode = new BvrolNode(*reinterpret_cast<BvrolNode*>(node)); break;
        case BVROR_NODE:                newNode = new BvrorNode(*reinterpret_cast<BvrorNode*>(node)); break;
        case BVSDIV_NODE:               newNode = new BvsdivNode(*reinterpret_cast<BvsdivNode*>(node)); break;
        case BVSGE_NODE:                newNode = new BvsgeNode(*reinterpret_cast<BvsgeNode*>(node)); break;
        case BVSGT_NODE:                newNode = new BvsgtNode(*reinterpret_cast<BvsgtNode*>(node)); break;
        case BVSHL_NODE:                newNode = new BvshlNode(*reinterpret_cast<BvshlNode*>(node)); break;
        case BVSLE_NODE:                newNode = new BvsleNode(*reinterpret_cast<BvsleNode*>(node)); break;
        case BVSLT_NODE:                newNode = new BvsltNode(*reinterpret_cast<BvsltNode*>(node)); break;
        case BVSMOD_NODE:               newNode = new BvsmodNode(*reinterpret_cast<BvsmodNode*>(node)); break;
        case BVSREM_NODE:               newNode = new BvsremNode(*reinterpret_cast<BvsremNode*>(node)); break;
        case BVSUB_NODE:                newNode = new BvsubNode(*reinterpret_cast<BvsubNode*>(node)); break;
        case BVUDIV_NODE:               newNode = new BvudivNode(*reinterpret_cast<BvudivNode*>(node)); break;
        case BVUGE_NODE:                newNode = new BvugeNode(*reinterpret_cast<BvugeNode*>(node)); break;
        case BVUGT_NODE:                newNode = new BvugtNode(*reinterpret_cast<BvugtNode*>(node)); break;
        case BVULE_NODE:                newNode = new BvuleNode(*reinterpret_cast<BvuleNode*>(node)); break;
        case BVULT_NODE:                newNode = new BvultNode(*reinterpret_cast<BvultNode*>(node)); break;
        case BVUREM_NODE:               newNode = new BvuremNode(*reinterpret_cast<BvuremNode*>(node)); break;
        case BVXNOR_NODE:               newNode = new BvxnorNode(*reinterpret_cast<BvxnorNode*>(node)); break;
        case BVXOR_NODE:                newNode = new BvxorNode(*reinterpret_cast<BvxorNode*>(node)); break;
        case BV_NODE:                   newNode = new BvNode(*reinterpret_cast<BvNode*>(node)); break;
        case COMPOUND_NODE:             newNode = new CompoundNode(*reinterpret_cast<CompoundNode*>(node)); break;
        case CONCAT_NODE:               newNode = new ConcatNode(*reinterpret_cast<ConcatNode*>(node)); break;
        case DECIMAL_NODE:              newNode = new DecimalNode(*reinterpret_cast<DecimalNode*>(node)); break;
        case DECLARE_FUNCTION_NODE:     newNode = new DeclareFunctionNode(*reinterpret_cast<DeclareFunctionNode*>(node)); break;
        case DISTINCT_NODE:             newNode = new DistinctNode(*reinterpret_cast<DistinctNode*>(node)); break;
        case EQUAL_NODE:                newNode = new EqualNode(*reinterpret_cast<EqualNode*>(node)); break;
        case EXTRACT_NODE:              newNode = new ExtractNode(*reinterpret_cast<ExtractNode*>(node)); break;
        case ITE_NODE:                  newNode = new IteNode(*reinterpret_cast<IteNode*>(node)); break;
        case LAND_NODE:                 newNode = new LandNode(*reinterpret_cast<LandNode*>(node)); break;
        case LET_NODE:                  newNode = new LetNode(*reinterpret_cast<LetNode*>(node)); break;
        case LNOT_NODE:                 newNode = new LnotNode(*reinterpret_cast<LnotNode*>(node)); break;
        case LOR_NODE:                  newNode = new LorNode(*reinterpret_cast<LorNode*>(node)); break;
        case REFERENCE_NODE:            newNode = new ReferenceNode(*reinterpret_cast<ReferenceNode*>(node)); break;
        case STRING_NODE:               newNode = new StringNode(*reinterpret_cast<StringNode*>(node)); break;
        case SX_NODE:                   newNode = new SxNode(*reinterpret_cast<SxNode*>(node)); break;
        case VARIABLE_NODE:             newNode = new VariableNode(*reinterpret_cast<VariableNode*>(node)); break;
        case ZX_NODE:                   newNode = new ZxNode(*reinterpret_cast<ZxNode*>(node)); break;
        default:
          throw std::invalid_argument("triton::ast::newInstance(): Invalid kind node.");
      }
      if (newNode == nullptr)
        throw std::invalid_argument("triton::ast::newInstance(): No enough memory.");
      return recordNode(node);
    }

  }; /* ast namespace */
}; /* triton namespace */

