//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cmath>

#include "api.hpp"
#include "smt2lib.hpp"
#include "smt2libZ3Ast.hpp"
#include "smt2libZ3Result.hpp"



namespace triton {
  namespace smt2lib {

    /* ====== Abstract node */

    smtAstAbstractNode::smtAstAbstractNode(enum kind_e kind) {
      this->kind = kind;
    }


    smtAstAbstractNode::smtAstAbstractNode() {
      this->kind = UNDEFINED_NODE;
    }


    smtAstAbstractNode::smtAstAbstractNode(const smtAstAbstractNode &copy) {
      this->kind = copy.kind;
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
      Z3Ast ast;
      Z3Result result = ast.eval(*this);
      return result.getBitvectorSize();
    }


    std::vector<smtAstAbstractNode *> &smtAstAbstractNode::getChilds(void) {
      return this->childs;
    }


    void smtAstAbstractNode::addChild(smtAstAbstractNode *child) {
      this->childs.push_back(child);
    }


    /* ====== assert */


    smtAstAssertNode::smtAstAssertNode(smtAstAbstractNode *expr) {
      this->kind = ASSERT_NODE;
      this->addChild(expr);
    }


    smtAstAssertNode::smtAstAssertNode(const smtAstAssertNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstAssertNode::~smtAstAssertNode() {
    }


    void smtAstAssertNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstAssertNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }

    /* ====== bvadd */


    smtAstBvaddNode::smtAstBvaddNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVADD_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvaddNode::smtAstBvaddNode(const smtAstBvaddNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvaddNode::~smtAstBvaddNode() {
    }


    void smtAstBvaddNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvaddNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvand */


    smtAstBvandNode::smtAstBvandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVAND_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvandNode::smtAstBvandNode(const smtAstBvandNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvandNode::~smtAstBvandNode() {
    }


    void smtAstBvandNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvandNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }



    /* ====== bvashr */


    smtAstBvashrNode::smtAstBvashrNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVASHR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvashrNode::smtAstBvashrNode(const smtAstBvashrNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvashrNode::~smtAstBvashrNode() {
    }


    void smtAstBvashrNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvashrNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvlshr */


    smtAstBvlshrNode::smtAstBvlshrNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVLSHR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvlshrNode::smtAstBvlshrNode(const smtAstBvlshrNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvlshrNode::~smtAstBvlshrNode() {
    }


    void smtAstBvlshrNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvlshrNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvmul */


    smtAstBvmulNode::smtAstBvmulNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVMUL_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvmulNode::smtAstBvmulNode(const smtAstBvmulNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvmulNode::~smtAstBvmulNode() {
    }


    void smtAstBvmulNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvmulNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvnand */


    smtAstBvnandNode::smtAstBvnandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVNAND_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvnandNode::smtAstBvnandNode(const smtAstBvnandNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnandNode::~smtAstBvnandNode() {
    }


    void smtAstBvnandNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnandNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvneg */


    smtAstBvnegNode::smtAstBvnegNode(smtAstAbstractNode *expr) {
      this->kind = BVNEG_NODE;
      this->addChild(expr);
    }


    smtAstBvnegNode::smtAstBvnegNode(const smtAstBvnegNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnegNode::~smtAstBvnegNode() {
    }


    void smtAstBvnegNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnegNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvnor */


    smtAstBvnorNode::smtAstBvnorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVNOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvnorNode::smtAstBvnorNode(const smtAstBvnorNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnorNode::~smtAstBvnorNode() {
    }


    void smtAstBvnorNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvnot */


    smtAstBvnotNode::smtAstBvnotNode(smtAstAbstractNode *expr) {
      this->kind = BVNOT_NODE;
      this->addChild(expr);
    }


    smtAstBvnotNode::smtAstBvnotNode(const smtAstBvnotNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvnotNode::~smtAstBvnotNode() {
    }


    void smtAstBvnotNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvnotNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvor */


    smtAstBvorNode::smtAstBvorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvorNode::smtAstBvorNode(const smtAstBvorNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvorNode::~smtAstBvorNode() {
    }


    void smtAstBvorNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvrol */


    smtAstBvrolNode::smtAstBvrolNode(triton::uint32 rot, smtAstAbstractNode *expr) {
      this->kind = BVROL_NODE;
      this->addChild(decimal(rot));
      this->addChild(expr);
    }


    smtAstBvrolNode::smtAstBvrolNode(const smtAstBvrolNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvrolNode::smtAstBvrolNode(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
      if (rot->getKind() != DECIMAL_NODE)
        throw std::runtime_error("smtAstBvrolNode - rot must be a decimal expression");
      this->kind = BVROL_NODE;
      this->addChild(rot);
      this->addChild(expr);
    }


    smtAstBvrolNode::~smtAstBvrolNode() {
    }


    void smtAstBvrolNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvrolNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvror */


    smtAstBvrorNode::smtAstBvrorNode(triton::uint32 rot, smtAstAbstractNode *expr) {
      this->kind = BVROR_NODE;
      this->addChild(decimal(rot));
      this->addChild(expr);
    }


    smtAstBvrorNode::smtAstBvrorNode(const smtAstBvrorNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvrorNode::smtAstBvrorNode(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
      if (rot->getKind() != DECIMAL_NODE)
        throw std::runtime_error("smtAstBvrorNode - rot must be a decimal expression");
      this->kind = BVROR_NODE;
      this->addChild(rot);
      this->addChild(expr);
    }


    smtAstBvrorNode::~smtAstBvrorNode() {
    }


    void smtAstBvrorNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvrorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsdiv */


    smtAstBvsdivNode::smtAstBvsdivNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSDIV_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsdivNode::smtAstBvsdivNode(const smtAstBvsdivNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsdivNode::~smtAstBvsdivNode() {
    }


    void smtAstBvsdivNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsdivNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsge */


    smtAstBvsgeNode::smtAstBvsgeNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSGE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsgeNode::smtAstBvsgeNode(const smtAstBvsgeNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsgeNode::~smtAstBvsgeNode() {
    }


    void smtAstBvsgeNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsgeNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsgt */


    smtAstBvsgtNode::smtAstBvsgtNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSGT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsgtNode::smtAstBvsgtNode(const smtAstBvsgtNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsgtNode::~smtAstBvsgtNode() {
    }


    void smtAstBvsgtNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsgtNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvshl */


    smtAstBvshlNode::smtAstBvshlNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSHL_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvshlNode::smtAstBvshlNode(const smtAstBvshlNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvshlNode::~smtAstBvshlNode() {
    }


    void smtAstBvshlNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvshlNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsle */


    smtAstBvsleNode::smtAstBvsleNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSLE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsleNode::smtAstBvsleNode(const smtAstBvsleNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsleNode::~smtAstBvsleNode() {
    }


    void smtAstBvsleNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsleNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvslt */


    smtAstBvsltNode::smtAstBvsltNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSLT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsltNode::smtAstBvsltNode(const smtAstBvsltNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsltNode::~smtAstBvsltNode() {
    }


    void smtAstBvsltNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsltNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsmod */


    smtAstBvsmodNode::smtAstBvsmodNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSMOD_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsmodNode::smtAstBvsmodNode(const smtAstBvsmodNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsmodNode::~smtAstBvsmodNode() {
    }


    void smtAstBvsmodNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsmodNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsrem */


    smtAstBvsremNode::smtAstBvsremNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSREM_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsremNode::smtAstBvsremNode(const smtAstBvsremNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsremNode::~smtAstBvsremNode() {
    }


    void smtAstBvsremNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsremNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvsub */


    smtAstBvsubNode::smtAstBvsubNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVSUB_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvsubNode::smtAstBvsubNode(const smtAstBvsubNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvsubNode::~smtAstBvsubNode() {
    }


    void smtAstBvsubNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvsubNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvudiv */


    smtAstBvudivNode::smtAstBvudivNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVUDIV_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvudivNode::smtAstBvudivNode(const smtAstBvudivNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvudivNode::~smtAstBvudivNode() {
    }


    void smtAstBvudivNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvudivNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvuge */


    smtAstBvugeNode::smtAstBvugeNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVUGE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvugeNode::smtAstBvugeNode(const smtAstBvugeNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvugeNode::~smtAstBvugeNode() {
    }


    void smtAstBvugeNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvugeNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvugt */


    smtAstBvugtNode::smtAstBvugtNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVUGT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvugtNode::smtAstBvugtNode(const smtAstBvugtNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvugtNode::~smtAstBvugtNode() {
    }


    void smtAstBvugtNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvugtNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvule */


    smtAstBvuleNode::smtAstBvuleNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVULE_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvuleNode::smtAstBvuleNode(const smtAstBvuleNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvuleNode::~smtAstBvuleNode() {
    }


    void smtAstBvuleNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvuleNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvult */


    smtAstBvultNode::smtAstBvultNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVULT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvultNode::smtAstBvultNode(const smtAstBvultNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvultNode::~smtAstBvultNode() {
    }


    void smtAstBvultNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvultNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvurem */


    smtAstBvuremNode::smtAstBvuremNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVUREM_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvuremNode::smtAstBvuremNode(const smtAstBvuremNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvuremNode::~smtAstBvuremNode() {
    }


    void smtAstBvuremNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvuremNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvxnor */


    smtAstBvxnorNode::smtAstBvxnorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVXNOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvxnorNode::smtAstBvxnorNode(const smtAstBvxnorNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvxnorNode::~smtAstBvxnorNode() {
    }


    void smtAstBvxnorNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvxnorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bvxor */


    smtAstBvxorNode::smtAstBvxorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = BVXOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstBvxorNode::smtAstBvxorNode(const smtAstBvxorNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvxorNode::~smtAstBvxorNode() {
    }


    void smtAstBvxorNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvxorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== bv */


    smtAstBvNode::smtAstBvNode(triton::uint128 value, triton::uint32 size) {
      this->kind = BV_NODE;
      this->addChild(decimal(value));
      this->addChild(decimal(size));
    }


    smtAstBvNode::smtAstBvNode(const smtAstBvNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstBvNode::~smtAstBvNode() {
    }


    void smtAstBvNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstBvNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== compound */


    smtAstCompoundNode::smtAstCompoundNode(std::vector<smtAstAbstractNode *> exprs) {
      this->kind = COMPOUND_NODE;
      for (triton::uint32 index = 0; index < exprs.size(); index++)
        this->addChild(exprs[index]);
    }


    smtAstCompoundNode::smtAstCompoundNode(const smtAstCompoundNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstCompoundNode::~smtAstCompoundNode() {
    }


    void smtAstCompoundNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstCompoundNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== concat */


    smtAstConcatNode::smtAstConcatNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = CONCAT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstConcatNode::smtAstConcatNode(const smtAstConcatNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstConcatNode::smtAstConcatNode(std::vector<smtAstAbstractNode *> exprs) {
      this->kind = CONCAT_NODE;

      triton::uint32 size = exprs.size();
      if (size < 2)
        throw std::length_error("smtAstConcatNode - exprs must contain at least two expressions");

      for (triton::uint32 index = 0; index < size; index++)
        this->addChild(exprs[index]);
    }


    smtAstConcatNode::smtAstConcatNode(std::list<smtAstAbstractNode *> exprs) {
      this->kind = CONCAT_NODE;

      if (exprs.size() < 2)
        throw std::length_error("smtAstConcatNode - exprs must contain at least two expressions");

      std::list<smtAstAbstractNode *>::iterator it = exprs.begin();
      for ( ; it != exprs.end(); it++)
        this->addChild(*it);
    }


    smtAstConcatNode::~smtAstConcatNode() {
    }


    void smtAstConcatNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstConcatNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Decimal node */


    smtAstDecimalNode::smtAstDecimalNode(triton::uint128 value) {
      this->kind  = DECIMAL_NODE;
      this->value = value;
    }


    smtAstDecimalNode::smtAstDecimalNode(const smtAstDecimalNode &copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
    }


    smtAstDecimalNode::~smtAstDecimalNode() {
    }


    triton::uint128 smtAstDecimalNode::getValue(void) {
      return this->value;
    }


    void smtAstDecimalNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstDecimalNode::hash(triton::uint32 deep) {
      triton::uint512 hash = this->kind ^ this->value;
      return hash;
    }


    /* ====== Declare node */


    smtAstDeclareNode::smtAstDeclareNode(std::string symVarName, triton::uint32 symVarSize) {
      this->kind = DECLARE_NODE;
      this->addChild(string(symVarName));
      this->addChild(decimal(symVarSize));
    }


    smtAstDeclareNode::smtAstDeclareNode(const smtAstDeclareNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstDeclareNode::~smtAstDeclareNode() {
    }


    void smtAstDeclareNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstDeclareNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Distinct node */


    smtAstDistinctNode::smtAstDistinctNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind  = DISTINCT_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstDistinctNode::smtAstDistinctNode(const smtAstDistinctNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstDistinctNode::~smtAstDistinctNode() {
    }


    void smtAstDistinctNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstDistinctNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== equal */


    smtAstEqualNode::smtAstEqualNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = EQUAL_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstEqualNode::smtAstEqualNode(const smtAstEqualNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstEqualNode::~smtAstEqualNode() {
    }


    void smtAstEqualNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstEqualNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== extract */


    smtAstExtractNode::smtAstExtractNode(triton::uint32 high, triton::uint32 low, smtAstAbstractNode *expr) {
      this->kind = EXTRACT_NODE;
      this->addChild(decimal(high));
      this->addChild(decimal(low));
      this->addChild(expr);
    }


    smtAstExtractNode::smtAstExtractNode(const smtAstExtractNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstExtractNode::~smtAstExtractNode() {
    }


    void smtAstExtractNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstExtractNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== ite */


    smtAstIteNode::smtAstIteNode(smtAstAbstractNode *ifExpr, smtAstAbstractNode *thenExpr, smtAstAbstractNode *elseExpr) {
      this->kind = ITE_NODE;
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
    }


    smtAstIteNode::smtAstIteNode(const smtAstIteNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstIteNode::~smtAstIteNode() {
    }


    void smtAstIteNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstIteNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Land */


    smtAstLandNode::smtAstLandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = LAND_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstLandNode::smtAstLandNode(const smtAstLandNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLandNode::~smtAstLandNode() {
    }


    void smtAstLandNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLandNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Lnot */


    smtAstLnotNode::smtAstLnotNode(smtAstAbstractNode *expr) {
      this->kind = LNOT_NODE;
      this->addChild(expr);
    }


    smtAstLnotNode::smtAstLnotNode(const smtAstLnotNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLnotNode::~smtAstLnotNode() {
    }


    void smtAstLnotNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLnotNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Lor */


    smtAstLorNode::smtAstLorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      this->kind = LOR_NODE;
      this->addChild(expr1);
      this->addChild(expr2);
    }


    smtAstLorNode::smtAstLorNode(const smtAstLorNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstLorNode::~smtAstLorNode() {
    }


    void smtAstLorNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstLorNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * this->childs[index]->hash(deep+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Reference node */


    smtAstReferenceNode::smtAstReferenceNode(triton::__uint value) {
      this->kind  = REFERENCE_NODE;
      this->value = value;
    }


    smtAstReferenceNode::smtAstReferenceNode(const smtAstReferenceNode &copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
    }


    smtAstReferenceNode::~smtAstReferenceNode() {
    }


    triton::__uint smtAstReferenceNode::getValue(void) {
      return this->value;
    }


    void smtAstReferenceNode::accept(Visitor& v) {
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
    }


    smtAstStringNode::smtAstStringNode(const smtAstStringNode &copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
    }


    smtAstStringNode::~smtAstStringNode() {
    }


    std::string smtAstStringNode::getValue(void) {
      return this->value;
    }


    void smtAstStringNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstStringNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::iterator it=this->value.begin(); it != this->value.end(); it++)
        h = h * triton::smt2lib::pow(*it, index++);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== sx */


    smtAstSxNode::smtAstSxNode(triton::uint32 sizeExt, smtAstAbstractNode *expr) {
      this->kind = SX_NODE;
      this->addChild(decimal(sizeExt));
      this->addChild(expr);
    }


    smtAstSxNode::smtAstSxNode(const smtAstSxNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstSxNode::~smtAstSxNode() {
    }


    void smtAstSxNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstSxNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== Variable node */


    smtAstVariableNode::smtAstVariableNode(std::string variable) {
      this->kind  = VARIABLE_NODE;
      this->value = variable;
    }


    smtAstVariableNode::smtAstVariableNode(const smtAstVariableNode &copy) {
      this->kind  = copy.kind;
      this->value = copy.value;
    }


    smtAstVariableNode::~smtAstVariableNode() {
    }


    std::string smtAstVariableNode::getValue(void) {
      return this->value;
    }


    void smtAstVariableNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstVariableNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind;
      triton::uint32 index = 1;
      for (std::string::iterator it=this->value.begin(); it != this->value.end(); it++)
        h = h * triton::smt2lib::pow(*it, index++);
      return triton::smt2lib::rotl(h, deep);
    }


    /* ====== zx */


    smtAstZxNode::smtAstZxNode(triton::uint32 sizeExt, smtAstAbstractNode *expr) {
      this->kind = ZX_NODE;
      this->addChild(decimal(sizeExt));
      this->addChild(expr);
    }


    smtAstZxNode::smtAstZxNode(const smtAstZxNode &copy) {
      this->kind = copy.kind;
      for (triton::uint32 index = 0; index < copy.childs.size(); index++)
        this->childs.push_back(copy.childs[index]);
    }


    smtAstZxNode::~smtAstZxNode() {
    }


    void smtAstZxNode::accept(Visitor& v) {
      v(*this);
    }


    triton::uint512 smtAstZxNode::hash(triton::uint32 deep) {
      triton::uint512 h = this->kind, s = this->childs.size();
      if (s) h = h * s;
      for (triton::uint32 index = 0; index < this->childs.size(); index++)
        h = h * triton::smt2lib::pow(this->childs[index]->hash(deep+1), index+1);
      return triton::smt2lib::rotl(h, deep);
    }

  }; /* smt2lib namespace */
}; /* triton namespace */



/* ====== Operators */

namespace triton {
  namespace smt2lib {

    /* Syntax dispatcher from an abstract node */
    std::ostream &operator<<(std::ostream &stream, smtAstAbstractNode *node) {
      switch (node->getKind()) {
        case ASSERT_NODE:     stream << reinterpret_cast<smtAstAssertNode *>(node); break;
        case BVADD_NODE:      stream << reinterpret_cast<smtAstBvaddNode *>(node); break;
        case BVAND_NODE:      stream << reinterpret_cast<smtAstBvandNode *>(node); break;
        case BVASHR_NODE:     stream << reinterpret_cast<smtAstBvashrNode *>(node); break;
        case BVLSHR_NODE:     stream << reinterpret_cast<smtAstBvlshrNode *>(node); break;
        case BVMUL_NODE:      stream << reinterpret_cast<smtAstBvmulNode *>(node); break;
        case BVNAND_NODE:     stream << reinterpret_cast<smtAstBvnandNode *>(node); break;
        case BVNEG_NODE:      stream << reinterpret_cast<smtAstBvnegNode *>(node); break;
        case BVNOR_NODE:      stream << reinterpret_cast<smtAstBvnorNode *>(node); break;
        case BVNOT_NODE:      stream << reinterpret_cast<smtAstBvnotNode *>(node); break;
        case BVOR_NODE:       stream << reinterpret_cast<smtAstBvorNode *>(node); break;
        case BVROL_NODE:      stream << reinterpret_cast<smtAstBvrolNode *>(node); break;
        case BVROR_NODE:      stream << reinterpret_cast<smtAstBvrorNode *>(node); break;
        case BVSDIV_NODE:     stream << reinterpret_cast<smtAstBvsdivNode *>(node); break;
        case BVSGE_NODE:      stream << reinterpret_cast<smtAstBvsgeNode *>(node); break;
        case BVSGT_NODE:      stream << reinterpret_cast<smtAstBvsgtNode *>(node); break;
        case BVSHL_NODE:      stream << reinterpret_cast<smtAstBvshlNode *>(node); break;
        case BVSLE_NODE:      stream << reinterpret_cast<smtAstBvsleNode *>(node); break;
        case BVSLT_NODE:      stream << reinterpret_cast<smtAstBvsltNode *>(node); break;
        case BVSMOD_NODE:     stream << reinterpret_cast<smtAstBvsmodNode *>(node); break;
        case BVSREM_NODE:     stream << reinterpret_cast<smtAstBvsremNode *>(node); break;
        case BVSUB_NODE:      stream << reinterpret_cast<smtAstBvsubNode *>(node); break;
        case BVUDIV_NODE:     stream << reinterpret_cast<smtAstBvudivNode *>(node); break;
        case BVUGE_NODE:      stream << reinterpret_cast<smtAstBvugeNode *>(node); break;
        case BVUGT_NODE:      stream << reinterpret_cast<smtAstBvugtNode *>(node); break;
        case BVULE_NODE:      stream << reinterpret_cast<smtAstBvuleNode *>(node); break;
        case BVULT_NODE:      stream << reinterpret_cast<smtAstBvultNode *>(node); break;
        case BVUREM_NODE:     stream << reinterpret_cast<smtAstBvuremNode *>(node); break;
        case BVXNOR_NODE:     stream << reinterpret_cast<smtAstBvxnorNode *>(node); break;
        case BVXOR_NODE:      stream << reinterpret_cast<smtAstBvxorNode *>(node); break;
        case BV_NODE:         stream << reinterpret_cast<smtAstBvNode *>(node); break;
        case COMPOUND_NODE:   stream << reinterpret_cast<smtAstCompoundNode *>(node); break;
        case CONCAT_NODE:     stream << reinterpret_cast<smtAstConcatNode *>(node); break;
        case DECIMAL_NODE:    stream << reinterpret_cast<smtAstDecimalNode *>(node); break;
        case DECLARE_NODE:    stream << reinterpret_cast<smtAstDeclareNode *>(node); break;
        case DISTINCT_NODE:   stream << reinterpret_cast<smtAstDistinctNode *>(node); break;
        case EQUAL_NODE:      stream << reinterpret_cast<smtAstEqualNode *>(node); break;
        case EXTRACT_NODE:    stream << reinterpret_cast<smtAstExtractNode *>(node); break;
        case ITE_NODE:        stream << reinterpret_cast<smtAstIteNode *>(node); break;
        case LAND_NODE:       stream << reinterpret_cast<smtAstLandNode *>(node); break;
        case LNOT_NODE:       stream << reinterpret_cast<smtAstLnotNode *>(node); break;
        case LOR_NODE:        stream << reinterpret_cast<smtAstLorNode *>(node); break;
        case REFERENCE_NODE:  stream << reinterpret_cast<smtAstReferenceNode *>(node); break;
        case STRING_NODE:     stream << reinterpret_cast<smtAstStringNode *>(node); break;
        case SX_NODE:         stream << reinterpret_cast<smtAstSxNode *>(node); break;
        case VARIABLE_NODE:   stream << reinterpret_cast<smtAstVariableNode *>(node); break;
        case ZX_NODE:         stream << reinterpret_cast<smtAstZxNode *>(node); break;
        default:
          throw std::invalid_argument("triton::smt2lib::operator<<(smtAstAbstractNode) - Invalid kind node");
      }
      return stream;
    }


    /* assert syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstAssertNode *node) {
      stream << "(assert " << node->getChilds()[0] << ")";
      return stream;
    }


    /* bvadd syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvaddNode *node) {
      stream << "(bvadd " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvand syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvandNode *node) {
      stream << "(bvand " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvashr syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvashrNode *node) {
      stream << "(bvashr " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvlshr syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvlshrNode *node) {
      stream << "(bvlshr " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvmul syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvmulNode *node) {
      stream << "(bvmul " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvnand syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvnandNode *node) {
      stream << "(bvnand " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvneg syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvnegNode *node) {
      stream << "(bvneg " << node->getChilds()[0] << ")";
      return stream;
    }


    /* bvnor syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvnorNode *node) {
      stream << "(bvnor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvnot syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvnotNode *node) {
      stream << "(bvnot " << node->getChilds()[0] << ")";
      return stream;
    }


    /* bvor syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvorNode *node) {
      stream << "(bvor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvrol syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvrolNode *node) {
      stream << "((_ rotate_left " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvror syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvrorNode *node) {
      stream << "((_ rotate_right " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsdiv syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsdivNode *node) {
      stream << "(bvsdiv " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsge syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsgeNode *node) {
      stream << "(bvsge " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsgt syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsgtNode *node) {
      stream << "(bvsgt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvshl syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvshlNode *node) {
      stream << "(bvshl " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsle syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsleNode *node) {
      stream << "(bvsle " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvslt syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsltNode *node) {
      stream << "(bvslt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsmod syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsmodNode *node) {
      stream << "(bvsmod " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsrem syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsremNode *node) {
      stream << "(bvsrem " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvsub syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvsubNode *node) {
      stream << "(bvsub " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvudiv syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvudivNode *node) {
      stream << "(bvudiv " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvuge syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvugeNode *node) {
      stream << "(bvuge " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvugt syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvugtNode *node) {
      stream << "(bvugt " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvule syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvuleNode *node) {
      stream << "(bvule " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvult syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvultNode *node) {
      stream << "(bvult " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvurem syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvuremNode *node) {
      stream << "(bvurem " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvxnor syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvxnorNode *node) {
      stream << "(bvxnor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bvxor syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvxorNode *node) {
      stream << "(bvxor " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* bv syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstBvNode *node) {
      stream << "(_ bv" << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* compound syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstCompoundNode *node) {
      for (triton::uint32 index = 0; index < node->getChilds().size(); index++)
        stream << node->getChilds()[index];
      return stream;
    }


    /* concat syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstConcatNode *node) {

      std::vector<smtAstAbstractNode *> childs = node->getChilds();
      triton::uint32 size = childs.size();

      if (size < 2)
        throw std::length_error("smtAstConcatNode - exprs must contain at least two expressions");

      stream << "(concat";
      for (triton::uint32 index = 0; index < size; index++)
        stream << " " << childs[index];
      stream << ")";

      return stream;
    }


    /* decimal syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstDecimalNode *node) {
      stream << node->getValue();
      return stream;
    }


    /* declare syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstDeclareNode *node) {
      stream << "(declare-fun " << node->getChilds()[0] << " () (_ BitVec " << node->getChilds()[1] << "))";
      return stream;
    }


    /* distinct syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstDistinctNode *node) {
      stream << "(distinct " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* equal syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstEqualNode *node) {
      stream << "(= " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* extract syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstExtractNode *node) {
      stream << "((_ extract " << node->getChilds()[0] << " " << node->getChilds()[1] << ") " << node->getChilds()[2] << ")";
      return stream;
    }


    /* ite syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstIteNode *node) {
      stream << "(ite " << node->getChilds()[0] << " " << node->getChilds()[1] << " " << node->getChilds()[2] << ")";
      return stream;
    }


    /* land syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstLandNode *node) {
      stream << "(and " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* lnot syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstLnotNode *node) {
      stream << "(not " << node->getChilds()[0] << ")";
      return stream;
    }


    /* lor syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstLorNode *node) {
      stream << "(or " << node->getChilds()[0] << " " << node->getChilds()[1] << ")";
      return stream;
    }


    /* reference syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstReferenceNode *node) {
      stream << "#" << node->getValue();
      return stream;
    }


    /* string syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstStringNode *node) {
      stream << node->getValue();
      return stream;
    }


    /* sx syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstSxNode *node) {
      stream << "((_ sign_extend " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
      return stream;
    }


    /* variable syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstVariableNode *node) {
      stream << node->getValue();
      return stream;
    }


    /* zx syntax */
    std::ostream &operator<<(std::ostream &stream, smtAstZxNode *node) {
      stream << "((_ zero_extend " << node->getChilds()[0] << ") " << node->getChilds()[1] << ")";
      return stream;
    }


    /* Compares two trees */
    bool operator==(smtAstAbstractNode& node1, smtAstAbstractNode& node2) {
      return node1.hash(1) == node2.hash(1);
    }


  }; /* smt2lib namespace */
}; /* triton namespace */



/* ====== Garbage collector utils */

namespace triton {
  namespace smt2lib {

    /* Global container. This container contains all allocated nodes. */
    std::set<smtAstAbstractNode*> allocatedNodes;


    /* Go through every allocated nodes and free them */
    void freeAllAstNodes(void) {
      std::set<smtAstAbstractNode*>::const_iterator it;
      for (it = triton::smt2lib::allocatedNodes.begin(); it != triton::smt2lib::allocatedNodes.end(); it++) {
        (*it)->getChilds().clear();
        delete *it;
      }
      triton::smt2lib::allocatedNodes.clear();
    }


    /* Frees a set of nodes and removes them from the global container. */
    void freeAstNodes(std::set<smtAstAbstractNode*>& nodes) {
      std::set<smtAstAbstractNode*>::iterator it;
      for (it = nodes.begin(); it != nodes.end(); it++) {
        triton::smt2lib::allocatedNodes.erase(*it);
        delete *it;
      }
      nodes.clear();
    }


    /* Extracts all unique nodes from a partial AST into the uniqueNodes set */
    void extractUniqueAstNodes(std::set<smtAstAbstractNode*>& uniqueNodes, smtAstAbstractNode* root) {
      std::vector<smtAstAbstractNode*>::const_iterator it;
      uniqueNodes.insert(root);
      for (it = root->getChilds().begin(); it != root->getChilds().end(); it++)
        triton::smt2lib::extractUniqueAstNodes(uniqueNodes, *it);
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
        triton::smt2lib::allocatedNodes.insert(node);
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

  }; /* smt2lib namespace */
}; /* triton namespace */



/* ====== Node builders */

namespace triton {
  namespace smt2lib {

    smtAstAbstractNode *smtAssert(smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstAssertNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bv(triton::uint128 value, triton::uint32 size) {
      smtAstAbstractNode *node = new smtAstBvNode(value, size);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvadd(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvaddNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvand(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvashr(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvashrNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvfalse(void) {
      smtAstAbstractNode *node = new smtAstBvNode(0, 1);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvlshr(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvlshrNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvmul(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvmulNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvnand(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvnandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvneg(smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstBvnegNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvnor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvnorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvnot(smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstBvnotNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvrol(triton::uint32 rot, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstBvrolNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvrol(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstBvrolNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvror(triton::uint32 rot, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstBvrorNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvror(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstBvrorNode(rot, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsdiv(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsdivNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsge(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsgeNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsgt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsgtNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvshl(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvshlNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsle(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsleNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvslt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsltNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsmod(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsmodNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsrem(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsremNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvsub(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvsubNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvtrue(void) {
      smtAstAbstractNode *node = new smtAstBvNode(1, 1);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvudiv(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvudivNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvuge(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvugeNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvugt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvugtNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvule(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvuleNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvult(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvultNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvurem(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvuremNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvxnor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvxnorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *bvxor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstBvxorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *compound(std::vector<smtAstAbstractNode*> exprs) {
      smtAstAbstractNode *node = new smtAstCompoundNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *concat(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstConcatNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *concat(std::vector<smtAstAbstractNode *> exprs) {
      smtAstAbstractNode *node = new smtAstConcatNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *concat(std::list<smtAstAbstractNode *> exprs) {
      smtAstAbstractNode *node = new smtAstConcatNode(exprs);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *decimal(triton::uint128 value) {
      smtAstAbstractNode *node = new smtAstDecimalNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *declare(std::string symVarName, triton::uint32 symVarSize) {
      smtAstAbstractNode *node = new smtAstDeclareNode(symVarName, symVarSize);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }

    smtAstAbstractNode *distinct(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstDistinctNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *equal(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstEqualNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *extract(triton::uint32 high, triton::uint32 low, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstExtractNode(high, low, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *ite(smtAstAbstractNode *ifExpr, smtAstAbstractNode *thenExpr, smtAstAbstractNode *elseExpr) {
      smtAstAbstractNode *node = new smtAstIteNode(ifExpr, thenExpr, elseExpr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *land(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstLandNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *lnot(smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstLnotNode(expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *lor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
      smtAstAbstractNode *node = new smtAstLorNode(expr1, expr2);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *reference(triton::__uint value) {
      smtAstAbstractNode *node = new smtAstReferenceNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *string(std::string value) {
      smtAstAbstractNode *node = new smtAstStringNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *sx(triton::uint32 sizeExt, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstSxNode(sizeExt, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *variable(std::string value) {
      smtAstAbstractNode *node = new smtAstVariableNode(value);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *zx(triton::uint32 sizeExt, smtAstAbstractNode *expr) {
      smtAstAbstractNode *node = new smtAstZxNode(sizeExt, expr);
      if (node == nullptr)
        throw std::runtime_error("Node builders - Not enough memory");
      return recordNode(node);
    }


    smtAstAbstractNode *newInstance(smtAstAbstractNode *node) {
      smtAstAbstractNode *newNode = nullptr;
      switch (node->getKind()) {
        case ASSERT_NODE:     newNode = new smtAstAssertNode(*reinterpret_cast<smtAstAssertNode *>(node)); break;
        case BVADD_NODE:      newNode = new smtAstBvaddNode(*reinterpret_cast<smtAstBvaddNode *>(node)); break;
        case BVAND_NODE:      newNode = new smtAstBvandNode(*reinterpret_cast<smtAstBvandNode *>(node)); break;
        case BVASHR_NODE:     newNode = new smtAstBvashrNode(*reinterpret_cast<smtAstBvashrNode *>(node)); break;
        case BVLSHR_NODE:     newNode = new smtAstBvlshrNode(*reinterpret_cast<smtAstBvlshrNode *>(node)); break;
        case BVMUL_NODE:      newNode = new smtAstBvmulNode(*reinterpret_cast<smtAstBvmulNode *>(node)); break;
        case BVNAND_NODE:     newNode = new smtAstBvnandNode(*reinterpret_cast<smtAstBvnandNode *>(node)); break;
        case BVNEG_NODE:      newNode = new smtAstBvnegNode(*reinterpret_cast<smtAstBvnegNode *>(node)); break;
        case BVNOR_NODE:      newNode = new smtAstBvnorNode(*reinterpret_cast<smtAstBvnorNode *>(node)); break;
        case BVNOT_NODE:      newNode = new smtAstBvnotNode(*reinterpret_cast<smtAstBvnotNode *>(node)); break;
        case BVOR_NODE:       newNode = new smtAstBvorNode(*reinterpret_cast<smtAstBvorNode *>(node)); break;
        case BVROL_NODE:      newNode = new smtAstBvrolNode(*reinterpret_cast<smtAstBvrolNode *>(node)); break;
        case BVROR_NODE:      newNode = new smtAstBvrorNode(*reinterpret_cast<smtAstBvrorNode *>(node)); break;
        case BVSDIV_NODE:     newNode = new smtAstBvsdivNode(*reinterpret_cast<smtAstBvsdivNode *>(node)); break;
        case BVSGE_NODE:      newNode = new smtAstBvsgeNode(*reinterpret_cast<smtAstBvsgeNode *>(node)); break;
        case BVSGT_NODE:      newNode = new smtAstBvsgtNode(*reinterpret_cast<smtAstBvsgtNode *>(node)); break;
        case BVSHL_NODE:      newNode = new smtAstBvshlNode(*reinterpret_cast<smtAstBvshlNode *>(node)); break;
        case BVSLE_NODE:      newNode = new smtAstBvsleNode(*reinterpret_cast<smtAstBvsleNode *>(node)); break;
        case BVSLT_NODE:      newNode = new smtAstBvsltNode(*reinterpret_cast<smtAstBvsltNode *>(node)); break;
        case BVSMOD_NODE:     newNode = new smtAstBvsmodNode(*reinterpret_cast<smtAstBvsmodNode *>(node)); break;
        case BVSREM_NODE:     newNode = new smtAstBvsremNode(*reinterpret_cast<smtAstBvsremNode *>(node)); break;
        case BVSUB_NODE:      newNode = new smtAstBvsubNode(*reinterpret_cast<smtAstBvsubNode *>(node)); break;
        case BVUDIV_NODE:     newNode = new smtAstBvudivNode(*reinterpret_cast<smtAstBvudivNode *>(node)); break;
        case BVUGE_NODE:      newNode = new smtAstBvugeNode(*reinterpret_cast<smtAstBvugeNode *>(node)); break;
        case BVUGT_NODE:      newNode = new smtAstBvugtNode(*reinterpret_cast<smtAstBvugtNode *>(node)); break;
        case BVULE_NODE:      newNode = new smtAstBvuleNode(*reinterpret_cast<smtAstBvuleNode *>(node)); break;
        case BVULT_NODE:      newNode = new smtAstBvultNode(*reinterpret_cast<smtAstBvultNode *>(node)); break;
        case BVUREM_NODE:     newNode = new smtAstBvuremNode(*reinterpret_cast<smtAstBvuremNode *>(node)); break;
        case BVXNOR_NODE:     newNode = new smtAstBvxnorNode(*reinterpret_cast<smtAstBvxnorNode *>(node)); break;
        case BVXOR_NODE:      newNode = new smtAstBvxorNode(*reinterpret_cast<smtAstBvxorNode *>(node)); break;
        case BV_NODE:         newNode = new smtAstBvNode(*reinterpret_cast<smtAstBvNode *>(node)); break;
        case COMPOUND_NODE:   newNode = new smtAstCompoundNode(*reinterpret_cast<smtAstCompoundNode *>(node)); break;
        case CONCAT_NODE:     newNode = new smtAstConcatNode(*reinterpret_cast<smtAstConcatNode *>(node)); break;
        case DECIMAL_NODE:    newNode = new smtAstDecimalNode(*reinterpret_cast<smtAstDecimalNode *>(node)); break;
        case DECLARE_NODE:    newNode = new smtAstDeclareNode(*reinterpret_cast<smtAstDeclareNode *>(node)); break;
        case DISTINCT_NODE:   newNode = new smtAstDistinctNode(*reinterpret_cast<smtAstDistinctNode *>(node)); break;
        case EQUAL_NODE:      newNode = new smtAstEqualNode(*reinterpret_cast<smtAstEqualNode *>(node)); break;
        case EXTRACT_NODE:    newNode = new smtAstExtractNode(*reinterpret_cast<smtAstExtractNode *>(node)); break;
        case ITE_NODE:        newNode = new smtAstIteNode(*reinterpret_cast<smtAstIteNode *>(node)); break;
        case LAND_NODE:       newNode = new smtAstLandNode(*reinterpret_cast<smtAstLandNode *>(node)); break;
        case LNOT_NODE:       newNode = new smtAstLnotNode(*reinterpret_cast<smtAstLnotNode *>(node)); break;
        case LOR_NODE:        newNode = new smtAstLorNode(*reinterpret_cast<smtAstLorNode *>(node)); break;
        case REFERENCE_NODE:  newNode = new smtAstReferenceNode(*reinterpret_cast<smtAstReferenceNode *>(node)); break;
        case STRING_NODE:     newNode = new smtAstStringNode(*reinterpret_cast<smtAstStringNode *>(node)); break;
        case SX_NODE:         newNode = new smtAstSxNode(*reinterpret_cast<smtAstSxNode *>(node)); break;
        case VARIABLE_NODE:   newNode = new smtAstVariableNode(*reinterpret_cast<smtAstVariableNode *>(node)); break;
        case ZX_NODE:         newNode = new smtAstZxNode(*reinterpret_cast<smtAstZxNode *>(node)); break;
        default:
          throw std::invalid_argument("triton::smt2lib::newInstance() - Invalid kind node");
      }
      if (newNode == nullptr)
        throw std::invalid_argument("triton::smt2lib::newInstance() - No enough memory");
      return recordNode(node);
    }

  }; /* smt2lib namespace */
}; /* triton namespace */

