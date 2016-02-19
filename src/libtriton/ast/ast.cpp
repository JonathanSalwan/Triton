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
      this->kind = kind;
      this->size = 0;
    }


    AbstractNode::AbstractNode() {
      this->kind = UNDEFINED_NODE;
      this->size = 0;
    }


    AbstractNode::AbstractNode(const AbstractNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
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


    std::vector<AbstractNode*>& AbstractNode::getChilds(void) {
      return this->childs;
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
      this->size = 1;
      this->addChild(expr);
    }


    AssertNode::AssertNode(const AssertNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    AssertNode::~AssertNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvaddNode::BvaddNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvaddNode::BvaddNode(const BvaddNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvaddNode::~BvaddNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvandNode::BvandNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvandNode::BvandNode(const BvandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvandNode::~BvandNode() {
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



    /* ====== bvashr */


    BvashrNode::BvashrNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVASHR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvashrNode::BvashrNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvashrNode::BvashrNode(const BvashrNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvashrNode::~BvashrNode() {
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
      if (!size)
        throw std::runtime_error("BvdeclNode::BvdeclNode(): Size connot be equal to zero.");
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("BvdeclNode::BvdeclNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->size = size;
      this->addChild(triton::ast::decimal(size));
    }


    BvdeclNode::BvdeclNode(const BvdeclNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvdeclNode::~BvdeclNode() {
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


    /* ====== bvlshr */


    BvlshrNode::BvlshrNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVLSHR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvlshrNode::BvlshrNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvlshrNode::BvlshrNode(const BvlshrNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvlshrNode::~BvlshrNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvmulNode::BvmulNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvmulNode::BvmulNode(const BvmulNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvmulNode::~BvmulNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvnandNode::BvnandNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvnandNode::BvnandNode(const BvnandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvnandNode::~BvnandNode() {
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
      this->size = expr->getBitvectorSize();
      this->addChild(expr);
    }


    BvnegNode::BvnegNode(const BvnegNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvnegNode::~BvnegNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvnorNode::BvnorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvnorNode::BvnorNode(const BvnorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvnorNode::~BvnorNode() {
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
      this->size = expr->getBitvectorSize();
      this->addChild(expr);
    }


    BvnotNode::BvnotNode(const BvnotNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvnotNode::~BvnotNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvorNode::BvorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvorNode::BvorNode(const BvorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvorNode::~BvorNode() {
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
      this->size = expr->getBitvectorSize();
      this->addChild(triton::ast::decimal(rot));
      this->addChild(expr);
    }


    BvrolNode::BvrolNode(const BvrolNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvrolNode::BvrolNode(AbstractNode* rot, AbstractNode* expr) {
      if (rot->getKind() != DECIMAL_NODE)
        throw std::runtime_error("BvrolNode::BvrolNode(): rot must be a decimal expression.");
      this->kind = BVROL_NODE;
      this->addChild(rot);
      this->addChild(expr);
    }


    BvrolNode::~BvrolNode() {
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
      this->size = expr->getBitvectorSize();
      this->addChild(triton::ast::decimal(rot));
      this->addChild(expr);
    }


    BvrorNode::BvrorNode(const BvrorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvrorNode::BvrorNode(AbstractNode* rot, AbstractNode* expr) {
      if (rot->getKind() != DECIMAL_NODE)
        throw std::runtime_error("BvrorNode::BvrorNode(): rot must be a decimal expression.");
      this->kind = BVROR_NODE;
      this->addChild(rot);
      this->addChild(expr);
    }


    BvrorNode::~BvrorNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsdivNode::BvsdivNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsdivNode::BvsdivNode(const BvsdivNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsdivNode::~BvsdivNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsgeNode::BvsgeNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsgeNode::BvsgeNode(const BvsgeNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsgeNode::~BvsgeNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsgtNode::BvsgtNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsgtNode::BvsgtNode(const BvsgtNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsgtNode::~BvsgtNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvshlNode::BvshlNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvshlNode::BvshlNode(const BvshlNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvshlNode::~BvshlNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsleNode::BvsleNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsleNode::BvsleNode(const BvsleNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsleNode::~BvsleNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsltNode::BvsltNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsltNode::BvsltNode(const BvsltNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsltNode::~BvsltNode() {
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


    /* ====== bvsmod */


    BvsmodNode::BvsmodNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSMOD_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsmodNode::BvsmodNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsmodNode::BvsmodNode(const BvsmodNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsmodNode::~BvsmodNode() {
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


    /* ====== bvsrem */


    BvsremNode::BvsremNode(AbstractNode* expr1, AbstractNode* expr2) {
      this->kind = BVSREM_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsremNode::BvsremNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsremNode::BvsremNode(const BvsremNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsremNode::~BvsremNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvsubNode::BvsubNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvsubNode::BvsubNode(const BvsubNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvsubNode::~BvsubNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvudivNode::BvudivNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvudivNode::BvudivNode(const BvudivNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvudivNode::~BvudivNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvugeNode::BvugeNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvugeNode::BvugeNode(const BvugeNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvugeNode::~BvugeNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvugtNode::BvugtNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvugtNode::BvugtNode(const BvugtNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvugtNode::~BvugtNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvuleNode::BvuleNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvuleNode::BvuleNode(const BvuleNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvuleNode::~BvuleNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvultNode::BvultNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvultNode::BvultNode(const BvultNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvultNode::~BvultNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvuremNode::BvuremNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvuremNode::BvuremNode(const BvuremNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvuremNode::~BvuremNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("BvxnorNode::BvxnorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvxnorNode::BvxnorNode(const BvxnorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvxnorNode::~BvxnorNode() {
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
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize()) {
        std::cout << expr1 << std::endl;
        std::cout << expr2 << std::endl;
        throw std::runtime_error("BvxorNode::BvxorNode(): Must take two nodes of same size.");
      }
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    BvxorNode::BvxorNode(const BvxorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvxorNode::~BvxorNode() {
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
      if (!size)
        throw std::runtime_error("BvNode::BvNode(): Size connot be equal to zero.");
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("BvNode::BvNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->size = size;
      this->addChild(triton::ast::decimal(value));
      this->addChild(triton::ast::decimal(size));
    }


    BvNode::BvNode(const BvNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    BvNode::~BvNode() {
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
      this->size = 0;
      for (triton::uint32 index = 0; index < exprs.size(); index++)
        this->addChild(exprs[index]);
    }


    CompoundNode::CompoundNode(const CompoundNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    CompoundNode::~CompoundNode() {
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
      this->size = expr1->getBitvectorSize() + expr2->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("ConcatNode::ConcatNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->addChild(expr1);
      this->addChild(expr2);
    }


    ConcatNode::ConcatNode(const ConcatNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    ConcatNode::ConcatNode(std::vector<AbstractNode*> exprs) {
      this->kind = CONCAT_NODE;
      this->size = 0;

      if (exprs.size() < 2)
        throw std::length_error("ConcatNode::ConcatNode(): exprs must contain at least two expressions.");

      for (triton::uint32 index = 0; index < exprs.size(); index++) {
        this->addChild(exprs[index]);
        this->size += exprs[index]->getBitvectorSize();
      }
      if (this->size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("ConcatNode::ConcatNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
    }


    ConcatNode::ConcatNode(std::list<AbstractNode*> exprs) {
      this->kind = CONCAT_NODE;
      this->size = 0;

      if (exprs.size() < 2)
        throw std::length_error("ConcatNode::ConcatNode():  exprs must contain at least two expressions.");

      std::list<AbstractNode *>::iterator it = exprs.begin();
      for ( ; it != exprs.end(); it++) {
        this->addChild(*it);
        this->size += (*it)->getBitvectorSize();
      }
      if (this->size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("ConcatNode::ConcatNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
    }


    ConcatNode::~ConcatNode() {
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
      this->size  = 0;
    }


    DecimalNode::DecimalNode(const DecimalNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    DecimalNode::~DecimalNode() {
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
      if (bvDecl->getKind() != BVDECL_NODE)
        throw std::runtime_error("DeclareFunctionNode::DeclareFunctionNode(): The second argument must be a bitvector declaration.");
      this->size = bvDecl->getBitvectorSize();
      this->addChild(triton::ast::string(name));
      this->addChild(bvDecl);
    }


    DeclareFunctionNode::DeclareFunctionNode(const DeclareFunctionNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    DeclareFunctionNode::~DeclareFunctionNode() {
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
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    DistinctNode::DistinctNode(const DistinctNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    DistinctNode::~DistinctNode() {
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
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    EqualNode::EqualNode(const EqualNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    EqualNode::~EqualNode() {
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
      if (low > high)
        throw std::runtime_error("ExtractNode::ExtractNode(): The high bit must be greater than the low bit.");
      this->size = ((high - low) + 1);
      this->addChild(triton::ast::decimal(high));
      this->addChild(triton::ast::decimal(low));
      this->addChild(expr);
    }


    ExtractNode::ExtractNode(const ExtractNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    ExtractNode::~ExtractNode() {
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
      if (thenExpr->getBitvectorSize() != elseExpr->getBitvectorSize())
        throw std::runtime_error("IteNode::IteNode(): Must take two nodes of same size.");
      this->size = thenExpr->getBitvectorSize();
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
    }


    IteNode::IteNode(const IteNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    IteNode::~IteNode() {
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
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    LandNode::LandNode(const LandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    LandNode::~LandNode() {
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
      this->size = expr3->getBitvectorSize();
      this->addChild(triton::ast::string(alias));
      this->addChild(expr2);
      this->addChild(expr3);
    }


    LetNode::LetNode(const LetNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    LetNode::~LetNode() {
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
      this->size = 1;
      this->addChild(expr);
    }


    LnotNode::LnotNode(const LnotNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    LnotNode::~LnotNode() {
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
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    LorNode::LorNode(const LorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    LorNode::~LorNode() {
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
      if (!triton::api.isSymbolicExpressionIdExists(value))
        this->size = 0;
      else
        this->size = triton::api.getAstFromId(value)->getBitvectorSize();
    }


    ReferenceNode::ReferenceNode(const ReferenceNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    ReferenceNode::~ReferenceNode() {
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
      this->size  = 0;
    }


    StringNode::StringNode(const StringNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    StringNode::~StringNode() {
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
      this->size = sizeExt + expr->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("SxNode::SxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
    }


    SxNode::SxNode(const SxNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    SxNode::~SxNode() {
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
    }


    VariableNode::VariableNode(const VariableNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    VariableNode::~VariableNode() {
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
      this->size = sizeExt + expr->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("ZxNode::ZxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
    }


    ZxNode::ZxNode(const ZxNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    ZxNode::~ZxNode() {
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

