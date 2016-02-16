//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cmath>

#include "api.hpp"
#include "ast.hpp"
#include "tritonToZ3Ast.hpp"
#include "z3Result.hpp"



namespace triton {
  namespace ast {

    /* ====== Abstract node */

    smtAstAbstractNode::smtAstAbstractNode(enum kind_e kind) {
      this->kind = kind;
      this->size = 0;
    }


    smtAstAbstractNode::smtAstAbstractNode() {
      this->kind = UNDEFINED_NODE;
      this->size = 0;
    }


    smtAstAbstractNode::smtAstAbstractNode(const smtAstAbstractNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstAbstractNode::~smtAstAbstractNode() {
      /* virtual */
    }


    enum kind_e smtAstAbstractNode::getKind(void) {
      return this->kind;
    }


    triton::uint32 smtAstAbstractNode::getBitvectorSize(void) {
      return this->size;
    }


    triton::uint512 smtAstAbstractNode::getBitvectorMask(void) {
      triton::uint512 mask = -1;
      mask = mask >> (512 - this->size);
      return mask;
    }


    std::vector<smtAstAbstractNode*>& smtAstAbstractNode::getChilds(void) {
      return this->childs;
    }


    void smtAstAbstractNode::addChild(smtAstAbstractNode* child) {
      this->childs.push_back(child);
    }


    void smtAstAbstractNode::setBitvectorSize(triton::uint32 size) {
      this->size = size;
    }


    /* ====== assert */


    smtAstAssertNode::smtAstAssertNode(smtAstAbstractNode* expr) {
      this->kind = ASSERT_NODE;
      this->size = 1;
      this->addChild(expr);
    }


    smtAstAssertNode::smtAstAssertNode(const smtAstAssertNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstAssertNode::~smtAstAssertNode() {
    }


    void smtAstAssertNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstAssertNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }

    /* ====== bvadd */


    smtAstBvaddNode::smtAstBvaddNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVADD_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvaddNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvaddNode::smtAstBvaddNode(const smtAstBvaddNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvaddNode::~smtAstBvaddNode() {
    }


    void smtAstBvaddNode::accept(AstVisitor& v) {
       v(*this);
    }


    triton::uint512 smtAstBvaddNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvand */


    smtAstBvandNode::smtAstBvandNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVAND_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvandNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvandNode::smtAstBvandNode(const smtAstBvandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvandNode::~smtAstBvandNode() {
    }


    void smtAstBvandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvandNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }



    /* ====== bvashr */


    smtAstBvashrNode::smtAstBvashrNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVASHR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvashrNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvashrNode::smtAstBvashrNode(const smtAstBvashrNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvashrNode::~smtAstBvashrNode() {
    }


    void smtAstBvashrNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvashrNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvdecl */


    smtAstBvdeclNode::smtAstBvdeclNode(triton::uint32 size) {
      this->kind = BVDECL_NODE;
      if (!size)
        throw std::runtime_error("triton::ast::smtAstBvdeclNode(): Size connot be equal to zero.");
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstBvdeclNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->size = size;
      this->addChild(triton::ast::decimal(size));
    }


    smtAstBvdeclNode::smtAstBvdeclNode(const smtAstBvdeclNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvdeclNode::~smtAstBvdeclNode() {
    }


    void smtAstBvdeclNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvdeclNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvlshr */


    smtAstBvlshrNode::smtAstBvlshrNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVLSHR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvlshrNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvlshrNode::smtAstBvlshrNode(const smtAstBvlshrNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvlshrNode::~smtAstBvlshrNode() {
    }


    void smtAstBvlshrNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvlshrNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvmul */


    smtAstBvmulNode::smtAstBvmulNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVMUL_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvmulNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvmulNode::smtAstBvmulNode(const smtAstBvmulNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvmulNode::~smtAstBvmulNode() {
    }


    void smtAstBvmulNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvmulNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnand */


    smtAstBvnandNode::smtAstBvnandNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVNAND_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvnandNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvnandNode::smtAstBvnandNode(const smtAstBvnandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnandNode::~smtAstBvnandNode() {
    }


    void smtAstBvnandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnandNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvneg */


    smtAstBvnegNode::smtAstBvnegNode(smtAstAbstractNode* expr) {
      this->kind = BVNEG_NODE;
      this->size = expr->getBitvectorSize();
      this->addChild(expr);
    }


    smtAstBvnegNode::smtAstBvnegNode(const smtAstBvnegNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnegNode::~smtAstBvnegNode() {
    }


    void smtAstBvnegNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnegNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnor */


    smtAstBvnorNode::smtAstBvnorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVNOR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvnorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvnorNode::smtAstBvnorNode(const smtAstBvnorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnorNode::~smtAstBvnorNode() {
    }


    void smtAstBvnorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvnot */


    smtAstBvnotNode::smtAstBvnotNode(smtAstAbstractNode* expr) {
      this->kind = BVNOT_NODE;
      this->size = expr->getBitvectorSize();
      this->addChild(expr);
    }


    smtAstBvnotNode::smtAstBvnotNode(const smtAstBvnotNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnotNode::~smtAstBvnotNode() {
    }


    void smtAstBvnotNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnotNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvor */


    smtAstBvorNode::smtAstBvorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVOR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvorNode::smtAstBvorNode(const smtAstBvorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvorNode::~smtAstBvorNode() {
    }


    void smtAstBvorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvrol */


    smtAstBvrolNode::smtAstBvrolNode(triton::uint32 rot, smtAstAbstractNode* expr) {
      this->kind = BVROL_NODE;
      this->size = expr->getBitvectorSize();
      this->addChild(triton::ast::decimal(rot));
      this->addChild(expr);
    }


    smtAstBvrolNode::smtAstBvrolNode(const smtAstBvrolNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvrolNode::smtAstBvrolNode(smtAstAbstractNode* rot, smtAstAbstractNode* expr) {
      if (rot->getKind() != DECIMAL_NODE)
        throw std::runtime_error("smtAstBvrolNode - rot must be a decimal expression");
      this->kind = BVROL_NODE;
      this->addChild(rot);
      this->addChild(expr);
    }


    smtAstBvrolNode::~smtAstBvrolNode() {
    }


    void smtAstBvrolNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvrolNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvror */


    smtAstBvrorNode::smtAstBvrorNode(triton::uint32 rot, smtAstAbstractNode* expr) {
      this->kind = BVROR_NODE;
      this->size = expr->getBitvectorSize();
      this->addChild(triton::ast::decimal(rot));
      this->addChild(expr);
    }


    smtAstBvrorNode::smtAstBvrorNode(const smtAstBvrorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvrorNode::smtAstBvrorNode(smtAstAbstractNode* rot, smtAstAbstractNode* expr) {
      if (rot->getKind() != DECIMAL_NODE)
        throw std::runtime_error("smtAstBvrorNode - rot must be a decimal expression");
      this->kind = BVROR_NODE;
      this->addChild(rot);
      this->addChild(expr);
    }


    smtAstBvrorNode::~smtAstBvrorNode() {
    }


    void smtAstBvrorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvrorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsdiv */


    smtAstBvsdivNode::smtAstBvsdivNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSDIV_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsdivNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsdivNode::smtAstBvsdivNode(const smtAstBvsdivNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsdivNode::~smtAstBvsdivNode() {
    }


    void smtAstBvsdivNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsdivNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsge */


    smtAstBvsgeNode::smtAstBvsgeNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSGE_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsgeNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsgeNode::smtAstBvsgeNode(const smtAstBvsgeNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsgeNode::~smtAstBvsgeNode() {
    }


    void smtAstBvsgeNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsgeNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsgt */


    smtAstBvsgtNode::smtAstBvsgtNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSGT_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsgtNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsgtNode::smtAstBvsgtNode(const smtAstBvsgtNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsgtNode::~smtAstBvsgtNode() {
    }


    void smtAstBvsgtNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsgtNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvshl */


    smtAstBvshlNode::smtAstBvshlNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSHL_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvshlNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvshlNode::smtAstBvshlNode(const smtAstBvshlNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvshlNode::~smtAstBvshlNode() {
    }


    void smtAstBvshlNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvshlNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsle */


    smtAstBvsleNode::smtAstBvsleNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSLE_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsleNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsleNode::smtAstBvsleNode(const smtAstBvsleNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsleNode::~smtAstBvsleNode() {
    }


    void smtAstBvsleNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsleNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvslt */


    smtAstBvsltNode::smtAstBvsltNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSLT_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsltNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsltNode::smtAstBvsltNode(const smtAstBvsltNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsltNode::~smtAstBvsltNode() {
    }


    void smtAstBvsltNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsltNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsmod */


    smtAstBvsmodNode::smtAstBvsmodNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSMOD_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsmodNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsmodNode::smtAstBvsmodNode(const smtAstBvsmodNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsmodNode::~smtAstBvsmodNode() {
    }


    void smtAstBvsmodNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsmodNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsrem */


    smtAstBvsremNode::smtAstBvsremNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSREM_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsremNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsremNode::smtAstBvsremNode(const smtAstBvsremNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsremNode::~smtAstBvsremNode() {
    }


    void smtAstBvsremNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsremNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvsub */


    smtAstBvsubNode::smtAstBvsubNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVSUB_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvsubNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsubNode::smtAstBvsubNode(const smtAstBvsubNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsubNode::~smtAstBvsubNode() {
    }


    void smtAstBvsubNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsubNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvudiv */


    smtAstBvudivNode::smtAstBvudivNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVUDIV_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvudivNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvudivNode::smtAstBvudivNode(const smtAstBvudivNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvudivNode::~smtAstBvudivNode() {
    }


    void smtAstBvudivNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvudivNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvuge */


    smtAstBvugeNode::smtAstBvugeNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVUGE_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvugeNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvugeNode::smtAstBvugeNode(const smtAstBvugeNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvugeNode::~smtAstBvugeNode() {
    }


    void smtAstBvugeNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvugeNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvugt */


    smtAstBvugtNode::smtAstBvugtNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVUGT_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvugtNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvugtNode::smtAstBvugtNode(const smtAstBvugtNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvugtNode::~smtAstBvugtNode() {
    }


    void smtAstBvugtNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvugtNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvule */


    smtAstBvuleNode::smtAstBvuleNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVULE_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvuleNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvuleNode::smtAstBvuleNode(const smtAstBvuleNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvuleNode::~smtAstBvuleNode() {
    }


    void smtAstBvuleNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvuleNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvult */


    smtAstBvultNode::smtAstBvultNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVULT_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvultNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvultNode::smtAstBvultNode(const smtAstBvultNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvultNode::~smtAstBvultNode() {
    }


    void smtAstBvultNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvultNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvurem */


    smtAstBvuremNode::smtAstBvuremNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVUREM_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvuremNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvuremNode::smtAstBvuremNode(const smtAstBvuremNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvuremNode::~smtAstBvuremNode() {
    }


    void smtAstBvuremNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvuremNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxnor */


    smtAstBvxnorNode::smtAstBvxnorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVXNOR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvxnorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvxnorNode::smtAstBvxnorNode(const smtAstBvxnorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvxnorNode::~smtAstBvxnorNode() {
    }


    void smtAstBvxnorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvxnorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bvxor */


    smtAstBvxorNode::smtAstBvxorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = BVXOR_NODE;
      if (expr1->getBitvectorSize() != expr2->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstBvxorNode(): Must take two nodes of same size.");
      this->size = expr1->getBitvectorSize();
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvxorNode::smtAstBvxorNode(const smtAstBvxorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvxorNode::~smtAstBvxorNode() {
    }


    void smtAstBvxorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvxorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== bv */


    smtAstBvNode::smtAstBvNode(triton::uint128 value, triton::uint32 size) {
      this->kind = BV_NODE;
      if (!size)
        throw std::runtime_error("triton::ast::smtAstBvNode(): Size connot be equal to zero.");
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstBvNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->size = size;
      this->addChild(triton::ast::decimal(value));
      this->addChild(triton::ast::decimal(size));
    }


    smtAstBvNode::smtAstBvNode(const smtAstBvNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvNode::~smtAstBvNode() {
    }


    void smtAstBvNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== compound */


    smtAstCompoundNode::smtAstCompoundNode(std::vector<smtAstAbstractNode*> exprs) {
      this->kind = COMPOUND_NODE;
      this->size = 0;
      for (triton::uint32 index = 0; index < exprs.size(); index++)
        this->addChild(exprs[index]);
    }


    smtAstCompoundNode::smtAstCompoundNode(const smtAstCompoundNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstCompoundNode::~smtAstCompoundNode() {
    }


    void smtAstCompoundNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstCompoundNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== concat */


    smtAstConcatNode::smtAstConcatNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = CONCAT_NODE;
      this->size = expr1->getBitvectorSize() + expr2->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstConcatNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstConcatNode::smtAstConcatNode(const smtAstConcatNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstConcatNode::smtAstConcatNode(std::vector<smtAstAbstractNode*> exprs) {
      this->kind = CONCAT_NODE;
      this->size = 0;

      if (exprs.size() < 2)
        throw std::length_error("smtAstConcatNode - exprs must contain at least two expressions");

      for (triton::uint32 index = 0; index < exprs.size(); index++) {
        this->addChild(exprs[index]);
        this->size += exprs[index]->getBitvectorSize();
      }
      if (this->size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstConcatNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
    }


    smtAstConcatNode::smtAstConcatNode(std::list<smtAstAbstractNode*> exprs) {
      this->kind = CONCAT_NODE;
      this->size = 0;

      if (exprs.size() < 2)
        throw std::length_error("smtAstConcatNode - exprs must contain at least two expressions");

      std::list<smtAstAbstractNode *>::iterator it = exprs.begin();
      for ( ; it != exprs.end(); it++) {
        this->addChild(*it);
        this->size += (*it)->getBitvectorSize();
      }
      if (this->size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstConcatNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
    }


    smtAstConcatNode::~smtAstConcatNode() {
    }


    void smtAstConcatNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstConcatNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Decimal node */


    smtAstDecimalNode::smtAstDecimalNode(triton::uint128 value) {
      this->kind  = DECIMAL_NODE;
      this->value = value;
      this->size  = 0;
    }


    smtAstDecimalNode::smtAstDecimalNode(const smtAstDecimalNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    smtAstDecimalNode::~smtAstDecimalNode() {
    }


    triton::uint128 smtAstDecimalNode::getValue(void) {
      return this->value;
    }


    void smtAstDecimalNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstDecimalNode::hash(triton::uint32 deep) {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== Declare node */


    smtAstDeclareFunctionNode::smtAstDeclareFunctionNode(std::string name, smtAstAbstractNode* bvDecl) {
      this->kind = DECLARE_FUNCTION_NODE;
      if (bvDecl->getKind() != BVDECL_NODE)
        throw std::runtime_error("smtAstDeclareFunctionNode - The second argument must be a bitvector declaration");
      this->size = bvDecl->getBitvectorSize();
      this->addChild(triton::ast::string(name));
      this->addChild(bvDecl);
    }


    smtAstDeclareFunctionNode::smtAstDeclareFunctionNode(const smtAstDeclareFunctionNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstDeclareFunctionNode::~smtAstDeclareFunctionNode() {
    }


    void smtAstDeclareFunctionNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstDeclareFunctionNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Distinct node */


    smtAstDistinctNode::smtAstDistinctNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = DISTINCT_NODE;
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstDistinctNode::smtAstDistinctNode(const smtAstDistinctNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstDistinctNode::~smtAstDistinctNode() {
    }


    void smtAstDistinctNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstDistinctNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== equal */


    smtAstEqualNode::smtAstEqualNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = EQUAL_NODE;
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstEqualNode::smtAstEqualNode(const smtAstEqualNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstEqualNode::~smtAstEqualNode() {
    }


    void smtAstEqualNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstEqualNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== extract */


    smtAstExtractNode::smtAstExtractNode(triton::uint32 high, triton::uint32 low, smtAstAbstractNode* expr) {
      this->kind = EXTRACT_NODE;
      if (low > high)
        throw std::runtime_error("triton::ast::smtAstExtractNode(): The high bit must be greater than the low bit.");
      this->size = ((high - low) + 1);
      this->addChild(triton::ast::decimal(high));
      this->addChild(triton::ast::decimal(low));
      this->addChild(expr);
    }


    smtAstExtractNode::smtAstExtractNode(const smtAstExtractNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstExtractNode::~smtAstExtractNode() {
    }


    void smtAstExtractNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstExtractNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== ite */


    smtAstIteNode::smtAstIteNode(smtAstAbstractNode* ifExpr, smtAstAbstractNode* thenExpr, smtAstAbstractNode* elseExpr) {
      this->kind = ITE_NODE;
      if (thenExpr->getBitvectorSize() != elseExpr->getBitvectorSize())
        throw std::runtime_error("triton::ast::smtAstIteNode(): Must take two nodes of same size.");
      this->size = thenExpr->getBitvectorSize();
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
    }


    smtAstIteNode::smtAstIteNode(const smtAstIteNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstIteNode::~smtAstIteNode() {
    }


    void smtAstIteNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstIteNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Land */


    smtAstLandNode::smtAstLandNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = LAND_NODE;
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstLandNode::smtAstLandNode(const smtAstLandNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLandNode::~smtAstLandNode() {
    }


    void smtAstLandNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLandNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Let */


    smtAstLetNode::smtAstLetNode(std::string alias, smtAstAbstractNode* expr2, smtAstAbstractNode* expr3) {
      this->kind = LET_NODE;
      this->size = expr3->getBitvectorSize();
      this->addChild(triton::ast::string(alias));
      this->addChild(expr2);
      this->addChild(expr3);
    }


    smtAstLetNode::smtAstLetNode(const smtAstLetNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLetNode::~smtAstLetNode() {
    }


    void smtAstLetNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLetNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lnot */


    smtAstLnotNode::smtAstLnotNode(smtAstAbstractNode* expr) {
      this->kind = LNOT_NODE;
      this->size = 1;
      this->addChild(expr);
    }


    smtAstLnotNode::smtAstLnotNode(const smtAstLnotNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLnotNode::~smtAstLnotNode() {
    }


    void smtAstLnotNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLnotNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Lor */


    smtAstLorNode::smtAstLorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      this->kind = LOR_NODE;
      this->size = 1;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstLorNode::smtAstLorNode(const smtAstLorNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLorNode::~smtAstLorNode() {
    }


    void smtAstLorNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Reference node */


    smtAstReferenceNode::smtAstReferenceNode(triton::__uint value) {
      this->kind  = REFERENCE_NODE;
      this->value = value;
      if (!triton::api.isSymbolicExpressionIdExists(value))
        this->size = 0;
      else
        this->size = triton::api.getAstFromId(value)->getBitvectorSize();
    }


    smtAstReferenceNode::smtAstReferenceNode(const smtAstReferenceNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    smtAstReferenceNode::~smtAstReferenceNode() {
    }


    triton::__uint smtAstReferenceNode::getValue(void) {
      return this->value;
    }


    void smtAstReferenceNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstReferenceNode::hash(triton::uint32 deep) {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== String node */


    smtAstStringNode::smtAstStringNode(std::string value) {
      this->kind  = STRING_NODE;
      this->value = value;
      this->size  = 0;
    }


    smtAstStringNode::smtAstStringNode(const smtAstStringNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    smtAstStringNode::~smtAstStringNode() {
    }


    std::string smtAstStringNode::getValue(void) {
      return this->value;
    }


    void smtAstStringNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstStringNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::iterator it=this->value.begin(); it != this->value.end(); it++)
        h = h * triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== sx */


    smtAstSxNode::smtAstSxNode(triton::uint32 sizeExt, smtAstAbstractNode* expr) {
      this->kind = SX_NODE;
      this->size = sizeExt + expr->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstSxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
    }


    smtAstSxNode::smtAstSxNode(const smtAstSxNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstSxNode::~smtAstSxNode() {
    }


    void smtAstSxNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstSxNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::ast::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::ast::rotl(h, deep);
    }


    /* ====== Variable node */


    smtAstVariableNode::smtAstVariableNode(std::string variable) {
      this->kind  = VARIABLE_NODE;
      this->value = variable;
      this->size  = 0;
    }


    smtAstVariableNode::smtAstVariableNode(const smtAstVariableNode& copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
      this->size  = copy.size;
    }


    smtAstVariableNode::~smtAstVariableNode() {
    }


    std::string smtAstVariableNode::getValue(void) {
      return this->value;
    }


    void smtAstVariableNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstVariableNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::iterator it=this->value.begin(); it != this->value.end(); it++)
        h = h * triton::ast::pow(*it, index++);
      return triton::ast::rotl(h, deep);
    }


    /* ====== zx */


    smtAstZxNode::smtAstZxNode(triton::uint32 sizeExt, smtAstAbstractNode* expr) {
      this->kind = ZX_NODE;
      this->size = sizeExt + expr->getBitvectorSize();
      if (size > MAX_BITS_SUPPORTED)
        throw std::runtime_error("triton::ast::smtAstZxNode(): Size connot be greater than MAX_BITS_SUPPORTED.");
      this->addChild(triton::ast::decimal(sizeExt));
      this->addChild(expr);
    }


    smtAstZxNode::smtAstZxNode(const smtAstZxNode& copy) {
      this->kind = copy.kind;
      this->size = copy.size;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstZxNode::~smtAstZxNode() {
    }


    void smtAstZxNode::accept(AstVisitor& v) {
      v(*this);
    }


    triton::uint512 smtAstZxNode::hash(triton::uint32 deep) {
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
    std::ostream& operator<<(std::ostream& stream, smtAstAbstractNode* node) {
      return triton::api.printAstRepresentation(stream, node);
    }


    /* Compares two trees */
    bool operator==(smtAstAbstractNode& node1, smtAstAbstractNode& node2) {
      return node1.hash(1) == node2.hash(1);
    }


  }; /* ast namespace */
}; /* triton namespace */



/* ====== Garbage collector utils */

namespace triton {
  namespace ast {

    /* Global container. This container contains all allocated nodes. */
    std::set<smtAstAbstractNode*> allocatedNodes;


    /* Go through every allocated nodes and free them */
    void freeAllAstNodes(void) {
      std::set<smtAstAbstractNode*>::const_iterator it;
      for (it = triton::ast::allocatedNodes.begin(); it != triton::ast::allocatedNodes.end(); it++) {
        (*it)->getChilds().clear();
        delete *it;
      }
      triton::ast::allocatedNodes.clear();
    }


    /* Frees a set of nodes and removes them from the global container. */
    void freeAstNodes(std::set<smtAstAbstractNode*>& nodes) {
      std::set<smtAstAbstractNode*>::iterator it;
      for (it = nodes.begin(); it != nodes.end(); it++) {
        triton::ast::allocatedNodes.erase(*it);
        delete *it;
      }
      nodes.clear();
    }


    /* Extracts all unique nodes from a partial AST into the uniqueNodes set */
    void extractUniqueAstNodes(std::set<smtAstAbstractNode*>& uniqueNodes, smtAstAbstractNode* root) {
      std::vector<smtAstAbstractNode*>::const_iterator it;
      uniqueNodes.insert(root);
      for (it = root->getChilds().begin(); it != root->getChilds().end(); it++)
        triton::ast::extractUniqueAstNodes(uniqueNodes, *it);
    }


    /* Records the allocated node or returns the same node if it already exists inside the summaries. */
    smtAstAbstractNode* recordNode(smtAstAbstractNode* node) {
      /* Check if the AST_SUMMARIES is enabled. */
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_SUMMARIES)) {
        smtAstAbstractNode* ret = triton::api.browseAstSummaries(node);
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

    smtAstAbstractNode* assert_(smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstAssertNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bv(triton::uint128 value, triton::uint32 size) {
      smtAstAbstractNode* node = new smtAstBvNode(value, size);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvadd(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvaddNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvand(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvashr(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvashrNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvdecl(triton::uint32 size) {
      smtAstAbstractNode* node = new smtAstBvdeclNode(size);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvfalse(void) {
      smtAstAbstractNode* node = new smtAstBvNode(0, 1);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvlshr(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvlshrNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvmul(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvmulNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvnand(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvnandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvneg(smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstBvnegNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvnor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvnorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvnot(smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstBvnotNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvrol(triton::uint32 rot, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstBvrolNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvrol(smtAstAbstractNode* rot, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstBvrolNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvror(triton::uint32 rot, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstBvrorNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvror(smtAstAbstractNode* rot, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstBvrorNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsdiv(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsdivNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsge(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsgeNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsgt(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsgtNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvshl(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvshlNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsle(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsleNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvslt(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsltNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsmod(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsmodNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsrem(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsremNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvsub(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvsubNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvtrue(void) {
      smtAstAbstractNode* node = new smtAstBvNode(1, 1);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvudiv(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvudivNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvuge(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvugeNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvugt(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvugtNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvule(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvuleNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvult(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvultNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvurem(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvuremNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


     smtAstAbstractNode* bvxnor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvxnorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* bvxor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstBvxorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* compound(std::vector<smtAstAbstractNode*> exprs) {
      smtAstAbstractNode* node = new smtAstCompoundNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* concat(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstConcatNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* concat(std::vector<smtAstAbstractNode*> exprs) {
      smtAstAbstractNode* node = new smtAstConcatNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* concat(std::list<smtAstAbstractNode*> exprs) {
      smtAstAbstractNode* node = new smtAstConcatNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* decimal(triton::uint128 value) {
      smtAstAbstractNode* node = new smtAstDecimalNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* declareFunction(std::string name, smtAstAbstractNode* bvDecl) {
      smtAstAbstractNode* node = new smtAstDeclareFunctionNode(name, bvDecl);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* distinct(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstDistinctNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* equal(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstEqualNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* extract(triton::uint32 high, triton::uint32 low, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstExtractNode(high, low, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* ite(smtAstAbstractNode* ifExpr, smtAstAbstractNode* thenExpr, smtAstAbstractNode* elseExpr) {
      smtAstAbstractNode* node = new smtAstIteNode(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* land(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstLandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* let(std::string alias, smtAstAbstractNode* expr2, smtAstAbstractNode* expr3) {
      smtAstAbstractNode* node = new smtAstLetNode(alias, expr2, expr3);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* lnot(smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstLnotNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* lor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2) {
      smtAstAbstractNode* node = new smtAstLorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* reference(triton::__uint value) {
      smtAstAbstractNode* node = new smtAstReferenceNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* string(std::string value) {
      smtAstAbstractNode* node = new smtAstStringNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* sx(triton::uint32 sizeExt, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstSxNode(sizeExt, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* variable(std::string value) {
      smtAstAbstractNode* node = new smtAstVariableNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* zx(triton::uint32 sizeExt, smtAstAbstractNode* expr) {
      smtAstAbstractNode* node = new smtAstZxNode(sizeExt, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode* newInstance(smtAstAbstractNode* node) {
      smtAstAbstractNode* newNode = nullptr;
      switch (node->getKind()) {
        case ASSERT_NODE:               newNode = new smtAstAssertNode(*reinterpret_cast<smtAstAssertNode*>(node)); break;
        case BVADD_NODE:                newNode = new smtAstBvaddNode(*reinterpret_cast<smtAstBvaddNode*>(node)); break;
        case BVAND_NODE:                newNode = new smtAstBvandNode(*reinterpret_cast<smtAstBvandNode*>(node)); break;
        case BVASHR_NODE:               newNode = new smtAstBvashrNode(*reinterpret_cast<smtAstBvashrNode*>(node)); break;
        case BVDECL_NODE:               newNode = new smtAstBvdeclNode(*reinterpret_cast<smtAstBvdeclNode*>(node)); break;
        case BVLSHR_NODE:               newNode = new smtAstBvlshrNode(*reinterpret_cast<smtAstBvlshrNode*>(node)); break;
        case BVMUL_NODE:                newNode = new smtAstBvmulNode(*reinterpret_cast<smtAstBvmulNode*>(node)); break;
        case BVNAND_NODE:               newNode = new smtAstBvnandNode(*reinterpret_cast<smtAstBvnandNode*>(node)); break;
        case BVNEG_NODE:                newNode = new smtAstBvnegNode(*reinterpret_cast<smtAstBvnegNode*>(node)); break;
        case BVNOR_NODE:                newNode = new smtAstBvnorNode(*reinterpret_cast<smtAstBvnorNode*>(node)); break;
        case BVNOT_NODE:                newNode = new smtAstBvnotNode(*reinterpret_cast<smtAstBvnotNode*>(node)); break;
        case BVOR_NODE:                 newNode = new smtAstBvorNode(*reinterpret_cast<smtAstBvorNode*>(node)); break;
        case BVROL_NODE:                newNode = new smtAstBvrolNode(*reinterpret_cast<smtAstBvrolNode*>(node)); break;
        case BVROR_NODE:                newNode = new smtAstBvrorNode(*reinterpret_cast<smtAstBvrorNode*>(node)); break;
        case BVSDIV_NODE:               newNode = new smtAstBvsdivNode(*reinterpret_cast<smtAstBvsdivNode*>(node)); break;
        case BVSGE_NODE:                newNode = new smtAstBvsgeNode(*reinterpret_cast<smtAstBvsgeNode*>(node)); break;
        case BVSGT_NODE:                newNode = new smtAstBvsgtNode(*reinterpret_cast<smtAstBvsgtNode*>(node)); break;
        case BVSHL_NODE:                newNode = new smtAstBvshlNode(*reinterpret_cast<smtAstBvshlNode*>(node)); break;
        case BVSLE_NODE:                newNode = new smtAstBvsleNode(*reinterpret_cast<smtAstBvsleNode*>(node)); break;
        case BVSLT_NODE:                newNode = new smtAstBvsltNode(*reinterpret_cast<smtAstBvsltNode*>(node)); break;
        case BVSMOD_NODE:               newNode = new smtAstBvsmodNode(*reinterpret_cast<smtAstBvsmodNode*>(node)); break;
        case BVSREM_NODE:               newNode = new smtAstBvsremNode(*reinterpret_cast<smtAstBvsremNode*>(node)); break;
        case BVSUB_NODE:                newNode = new smtAstBvsubNode(*reinterpret_cast<smtAstBvsubNode*>(node)); break;
        case BVUDIV_NODE:               newNode = new smtAstBvudivNode(*reinterpret_cast<smtAstBvudivNode*>(node)); break;
        case BVUGE_NODE:                newNode = new smtAstBvugeNode(*reinterpret_cast<smtAstBvugeNode*>(node)); break;
        case BVUGT_NODE:                newNode = new smtAstBvugtNode(*reinterpret_cast<smtAstBvugtNode*>(node)); break;
        case BVULE_NODE:                newNode = new smtAstBvuleNode(*reinterpret_cast<smtAstBvuleNode*>(node)); break;
        case BVULT_NODE:                newNode = new smtAstBvultNode(*reinterpret_cast<smtAstBvultNode*>(node)); break;
        case BVUREM_NODE:               newNode = new smtAstBvuremNode(*reinterpret_cast<smtAstBvuremNode*>(node)); break;
        case BVXNOR_NODE:               newNode = new smtAstBvxnorNode(*reinterpret_cast<smtAstBvxnorNode*>(node)); break;
        case BVXOR_NODE:                newNode = new smtAstBvxorNode(*reinterpret_cast<smtAstBvxorNode*>(node)); break;
        case BV_NODE:                   newNode = new smtAstBvNode(*reinterpret_cast<smtAstBvNode*>(node)); break;
        case COMPOUND_NODE:             newNode = new smtAstCompoundNode(*reinterpret_cast<smtAstCompoundNode*>(node)); break;
        case CONCAT_NODE:               newNode = new smtAstConcatNode(*reinterpret_cast<smtAstConcatNode*>(node)); break;
        case DECIMAL_NODE:              newNode = new smtAstDecimalNode(*reinterpret_cast<smtAstDecimalNode*>(node)); break;
        case DECLARE_FUNCTION_NODE:     newNode = new smtAstDeclareFunctionNode(*reinterpret_cast<smtAstDeclareFunctionNode*>(node)); break;
        case DISTINCT_NODE:             newNode = new smtAstDistinctNode(*reinterpret_cast<smtAstDistinctNode*>(node)); break;
        case EQUAL_NODE:                newNode = new smtAstEqualNode(*reinterpret_cast<smtAstEqualNode*>(node)); break;
        case EXTRACT_NODE:              newNode = new smtAstExtractNode(*reinterpret_cast<smtAstExtractNode*>(node)); break;
        case ITE_NODE:                  newNode = new smtAstIteNode(*reinterpret_cast<smtAstIteNode*>(node)); break;
        case LAND_NODE:                 newNode = new smtAstLandNode(*reinterpret_cast<smtAstLandNode*>(node)); break;
        case LET_NODE:                  newNode = new smtAstLetNode(*reinterpret_cast<smtAstLetNode*>(node)); break;
        case LNOT_NODE:                 newNode = new smtAstLnotNode(*reinterpret_cast<smtAstLnotNode*>(node)); break;
        case LOR_NODE:                  newNode = new smtAstLorNode(*reinterpret_cast<smtAstLorNode*>(node)); break;
        case REFERENCE_NODE:            newNode = new smtAstReferenceNode(*reinterpret_cast<smtAstReferenceNode*>(node)); break;
        case STRING_NODE:               newNode = new smtAstStringNode(*reinterpret_cast<smtAstStringNode*>(node)); break;
        case SX_NODE:                   newNode = new smtAstSxNode(*reinterpret_cast<smtAstSxNode*>(node)); break;
        case VARIABLE_NODE:             newNode = new smtAstVariableNode(*reinterpret_cast<smtAstVariableNode*>(node)); break;
        case ZX_NODE:                   newNode = new smtAstZxNode(*reinterpret_cast<smtAstZxNode*>(node)); break;
        default:
          throw std::invalid_argument("triton::ast::newInstance() - Invalid kind node");
      }
      if (newNode == nullptr)
        throw std::invalid_argument("triton::ast::newInstance() - No enough memory");
      return recordNode(node);
    }

  }; /* ast namespace */
}; /* triton namespace */

