/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include "SMT2Lib.h"

using namespace smt2lib;


// ====== Abstract node


smtAstAbstractNode::smtAstAbstractNode(enum kind_e kind) {
  this->kind = kind;
}


smtAstAbstractNode::smtAstAbstractNode() {
  this->kind = UNDEFINED_NODE;
}


smtAstAbstractNode::smtAstAbstractNode(const smtAstAbstractNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstAbstractNode::~smtAstAbstractNode() {
  freeAllNodes(this->childs);
}


enum kind_e smtAstAbstractNode::getKind(void) {
  return this->kind;
}


std::vector<smtAstAbstractNode *> &smtAstAbstractNode::getChilds(void) {
  return this->childs;
}


void smtAstAbstractNode::addChild(smtAstAbstractNode *child) {
  this->childs.push_back(child);
}


// ====== assert


smtAstAssertNode::smtAstAssertNode(smtAstAbstractNode *expr) {
  this->kind = ASSERT_NODE;
  this->addChild(expr);
}


smtAstAssertNode::smtAstAssertNode(const smtAstAssertNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstAssertNode::~smtAstAssertNode() {
  freeAllNodes(this->childs);
}

void smtAstAssertNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvadd


smtAstBvaddNode::smtAstBvaddNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVADD_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvaddNode::smtAstBvaddNode(const smtAstBvaddNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvaddNode::~smtAstBvaddNode() {
  freeAllNodes(this->childs);
}

void smtAstBvaddNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvand


smtAstBvandNode::smtAstBvandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVAND_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvandNode::smtAstBvandNode(const smtAstBvandNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvandNode::~smtAstBvandNode() {
  freeAllNodes(this->childs);
}

void smtAstBvandNode::accept(Visitor& v) {
  v(*this);
}



// ====== bvashr


smtAstBvashrNode::smtAstBvashrNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVASHR_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvashrNode::smtAstBvashrNode(const smtAstBvashrNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvashrNode::~smtAstBvashrNode() {
  freeAllNodes(this->childs);
}

void smtAstBvashrNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvlshr


smtAstBvlshrNode::smtAstBvlshrNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVLSHR_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvlshrNode::smtAstBvlshrNode(const smtAstBvlshrNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvlshrNode::~smtAstBvlshrNode() {
  freeAllNodes(this->childs);
}

void smtAstBvlshrNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvmul


smtAstBvmulNode::smtAstBvmulNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVMUL_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvmulNode::smtAstBvmulNode(const smtAstBvmulNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvmulNode::~smtAstBvmulNode() {
  freeAllNodes(this->childs);
}

void smtAstBvmulNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvnand


smtAstBvnandNode::smtAstBvnandNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVNAND_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvnandNode::smtAstBvnandNode(const smtAstBvnandNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvnandNode::~smtAstBvnandNode() {
  freeAllNodes(this->childs);
}

void smtAstBvnandNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvneg


smtAstBvnegNode::smtAstBvnegNode(smtAstAbstractNode *expr) {
  this->kind = BVNEG_NODE;
  this->addChild(expr);
}


smtAstBvnegNode::smtAstBvnegNode(const smtAstBvnegNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvnegNode::~smtAstBvnegNode() {
  freeAllNodes(this->childs);
}

void smtAstBvnegNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvnor


smtAstBvnorNode::smtAstBvnorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVNOR_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvnorNode::smtAstBvnorNode(const smtAstBvnorNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvnorNode::~smtAstBvnorNode() {
  freeAllNodes(this->childs);
}

void smtAstBvnorNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvnot


smtAstBvnotNode::smtAstBvnotNode(smtAstAbstractNode *expr) {
  this->kind = BVNOT_NODE;
  this->addChild(expr);
}


smtAstBvnotNode::smtAstBvnotNode(const smtAstBvnotNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvnotNode::~smtAstBvnotNode() {
  freeAllNodes(this->childs);
}

void smtAstBvnotNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvor


smtAstBvorNode::smtAstBvorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVOR_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvorNode::smtAstBvorNode(const smtAstBvorNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvorNode::~smtAstBvorNode() {
  freeAllNodes(this->childs);
}

void smtAstBvorNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvrol


smtAstBvrolNode::smtAstBvrolNode(uint64 rot, smtAstAbstractNode *expr) {
  this->kind = BVROL_NODE;
  this->addChild(new smtAstDecimalNode(rot));
  this->addChild(expr);
}


smtAstBvrolNode::smtAstBvrolNode(const smtAstBvrolNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvrolNode::smtAstBvrolNode(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
  if (rot->getKind() != DECIMAL_NODE)
    throw std::runtime_error("smtAstBvrolNode - rot must be a decimal expression");
  this->kind = BVROL_NODE;
  this->addChild(rot);
  this->addChild(expr);
}


smtAstBvrolNode::~smtAstBvrolNode() {
  freeAllNodes(this->childs);
}

void smtAstBvrolNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvror


smtAstBvrorNode::smtAstBvrorNode(uint64 rot, smtAstAbstractNode *expr) {
  this->kind = BVROR_NODE;
  this->addChild(new smtAstDecimalNode(rot));
  this->addChild(expr);
}


smtAstBvrorNode::smtAstBvrorNode(const smtAstBvrorNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvrorNode::smtAstBvrorNode(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
  if (rot->getKind() != DECIMAL_NODE)
    throw std::runtime_error("smtAstBvrorNode - rot must be a decimal expression");
  this->kind = BVROR_NODE;
  this->addChild(rot);
  this->addChild(expr);
}


smtAstBvrorNode::~smtAstBvrorNode() {
  freeAllNodes(this->childs);
}

void smtAstBvrorNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsdiv


smtAstBvsdivNode::smtAstBvsdivNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSDIV_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsdivNode::smtAstBvsdivNode(const smtAstBvsdivNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsdivNode::~smtAstBvsdivNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsdivNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsge


smtAstBvsgeNode::smtAstBvsgeNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSGE_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsgeNode::smtAstBvsgeNode(const smtAstBvsgeNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsgeNode::~smtAstBvsgeNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsgeNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsgt


smtAstBvsgtNode::smtAstBvsgtNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSGT_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsgtNode::smtAstBvsgtNode(const smtAstBvsgtNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsgtNode::~smtAstBvsgtNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsgtNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvshl


smtAstBvshlNode::smtAstBvshlNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSHL_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvshlNode::smtAstBvshlNode(const smtAstBvshlNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvshlNode::~smtAstBvshlNode() {
  freeAllNodes(this->childs);
}

void smtAstBvshlNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsle


smtAstBvsleNode::smtAstBvsleNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSLE_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsleNode::smtAstBvsleNode(const smtAstBvsleNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsleNode::~smtAstBvsleNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsleNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvslt


smtAstBvsltNode::smtAstBvsltNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSLT_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsltNode::smtAstBvsltNode(const smtAstBvsltNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsltNode::~smtAstBvsltNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsltNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsmod


smtAstBvsmodNode::smtAstBvsmodNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSMOD_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsmodNode::smtAstBvsmodNode(const smtAstBvsmodNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsmodNode::~smtAstBvsmodNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsmodNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsrem


smtAstBvsremNode::smtAstBvsremNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSREM_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsremNode::smtAstBvsremNode(const smtAstBvsremNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsremNode::~smtAstBvsremNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsremNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvsub


smtAstBvsubNode::smtAstBvsubNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVSUB_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvsubNode::smtAstBvsubNode(const smtAstBvsubNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvsubNode::~smtAstBvsubNode() {
  freeAllNodes(this->childs);
}

void smtAstBvsubNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvudiv


smtAstBvudivNode::smtAstBvudivNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVUDIV_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvudivNode::smtAstBvudivNode(const smtAstBvudivNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvudivNode::~smtAstBvudivNode() {
  freeAllNodes(this->childs);
}

void smtAstBvudivNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvuge


smtAstBvugeNode::smtAstBvugeNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVUGE_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvugeNode::smtAstBvugeNode(const smtAstBvugeNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvugeNode::~smtAstBvugeNode() {
  freeAllNodes(this->childs);
}

void smtAstBvugeNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvugt


smtAstBvugtNode::smtAstBvugtNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVUGT_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvugtNode::smtAstBvugtNode(const smtAstBvugtNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvugtNode::~smtAstBvugtNode() {
  freeAllNodes(this->childs);
}

void smtAstBvugtNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvule


smtAstBvuleNode::smtAstBvuleNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVULE_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvuleNode::smtAstBvuleNode(const smtAstBvuleNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvuleNode::~smtAstBvuleNode() {
  freeAllNodes(this->childs);
}

void smtAstBvuleNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvult


smtAstBvultNode::smtAstBvultNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVULT_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvultNode::smtAstBvultNode(const smtAstBvultNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvultNode::~smtAstBvultNode() {
  freeAllNodes(this->childs);
}

void smtAstBvultNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvurem


smtAstBvuremNode::smtAstBvuremNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVUREM_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvuremNode::smtAstBvuremNode(const smtAstBvuremNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvuremNode::~smtAstBvuremNode() {
  freeAllNodes(this->childs);
}

void smtAstBvuremNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvxnor


smtAstBvxnorNode::smtAstBvxnorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVXNOR_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvxnorNode::smtAstBvxnorNode(const smtAstBvxnorNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvxnorNode::~smtAstBvxnorNode() {
  freeAllNodes(this->childs);
}

void smtAstBvxnorNode::accept(Visitor& v) {
  v(*this);
}


// ====== bvxor


smtAstBvxorNode::smtAstBvxorNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = BVXOR_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstBvxorNode::smtAstBvxorNode(const smtAstBvxorNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvxorNode::~smtAstBvxorNode() {
  freeAllNodes(this->childs);
}

void smtAstBvxorNode::accept(Visitor& v) {
  v(*this);
}


// ====== bv


smtAstBvNode::smtAstBvNode(uint128 value, uint64 size) {
  this->kind = BV_NODE;
  this->addChild(new smtAstDecimalNode(value));
  this->addChild(new smtAstDecimalNode(size));
}


smtAstBvNode::smtAstBvNode(const smtAstBvNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstBvNode::~smtAstBvNode() {
  freeAllNodes(this->childs);
}

void smtAstBvNode::accept(Visitor& v) {
  v(*this);
}


// ====== compound


smtAstCompoundNode::smtAstCompoundNode(std::vector<smtAstAbstractNode *> exprs) {
  uint64 index = 0;
  this->kind = COMPOUND_NODE;
  for ( ; index < exprs.size(); index++)
    this->addChild(exprs[index]);
}


smtAstCompoundNode::smtAstCompoundNode(const smtAstCompoundNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstCompoundNode::~smtAstCompoundNode() {
  freeAllNodes(this->childs);
}

void smtAstCompoundNode::accept(Visitor& v) {
  v(*this);
}


// ====== concat


smtAstConcatNode::smtAstConcatNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = CONCAT_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstConcatNode::smtAstConcatNode(const smtAstConcatNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstConcatNode::smtAstConcatNode(std::vector<smtAstAbstractNode *> exprs) {
  this->kind = CONCAT_NODE;

  uint64 index;
  uint64 size = exprs.size();
  if (size < 2)
    throw std::length_error("smtAstConcatNode - exprs must contain at less two expressions");

  for (index = 0; index < size; index++)
    this->addChild(exprs[index]);
}


smtAstConcatNode::smtAstConcatNode(std::list<smtAstAbstractNode *> exprs) {
  this->kind = CONCAT_NODE;

  if (exprs.size() < 2)
    throw std::length_error("smtAstConcatNode - exprs must contain at less two expressions");

  std::list<smtAstAbstractNode *>::iterator it = exprs.begin();
  for ( ; it != exprs.end(); it++)
    this->addChild(*it);
}


smtAstConcatNode::~smtAstConcatNode() {
  freeAllNodes(this->childs);
}

void smtAstConcatNode::accept(Visitor& v) {
  v(*this);
}


// ====== Decimal node


smtAstDecimalNode::smtAstDecimalNode(uint128 value) {
  this->kind  = DECIMAL_NODE;
  this->value = value;
}


smtAstDecimalNode::smtAstDecimalNode(const smtAstDecimalNode &copy) {
  this->kind  = copy.kind;
  this->value = copy.value;
}


smtAstDecimalNode::~smtAstDecimalNode() {
  freeAllNodes(this->childs);
}


uint128 smtAstDecimalNode::getValue(void) {
  return this->value;
}

void smtAstDecimalNode::accept(Visitor& v) {
  v(*this);
}


// ====== Declare node


smtAstDeclareNode::smtAstDeclareNode(std::string symVarName, uint64 symVarSize) {
  this->kind = DECLARE_NODE;
  this->addChild(new smtAstStringNode(symVarName));
  this->addChild(new smtAstDecimalNode(symVarSize));
}


smtAstDeclareNode::smtAstDeclareNode(const smtAstDeclareNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstDeclareNode::~smtAstDeclareNode() {
  freeAllNodes(this->childs);
}

void smtAstDeclareNode::accept(Visitor& v) {
  v(*this);
}


// ====== Distinct node


smtAstDistinctNode::smtAstDistinctNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind  = DISTINCT_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstDistinctNode::smtAstDistinctNode(const smtAstDistinctNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstDistinctNode::~smtAstDistinctNode() {
  freeAllNodes(this->childs);
}

void smtAstDistinctNode::accept(Visitor& v) {
  v(*this);
}


// ====== equal


smtAstEqualNode::smtAstEqualNode(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
  this->kind = EQUAL_NODE;
  this->addChild(expr1);
  this->addChild(expr2);
}


smtAstEqualNode::smtAstEqualNode(const smtAstEqualNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstEqualNode::~smtAstEqualNode() {
  freeAllNodes(this->childs);
}

void smtAstEqualNode::accept(Visitor& v) {
  v(*this);
}


// ====== extract


smtAstExtractNode::smtAstExtractNode(uint64 high, uint64 low, smtAstAbstractNode *expr) {
  this->kind = EXTRACT_NODE;
  this->addChild(new smtAstDecimalNode(high));
  this->addChild(new smtAstDecimalNode(low));
  this->addChild(expr);
}


smtAstExtractNode::smtAstExtractNode(const smtAstExtractNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstExtractNode::~smtAstExtractNode() {
  freeAllNodes(this->childs);
}

void smtAstExtractNode::accept(Visitor& v) {
  v(*this);
}


// ====== ite


smtAstIteNode::smtAstIteNode(smtAstAbstractNode *ifExpr, smtAstAbstractNode *thenExpr, smtAstAbstractNode *elseExpr) {
  this->kind = ITE_NODE;
  this->addChild(ifExpr);
  this->addChild(thenExpr);
  this->addChild(elseExpr);
}


smtAstIteNode::smtAstIteNode(const smtAstIteNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstIteNode::~smtAstIteNode() {
  freeAllNodes(this->childs);
}

void smtAstIteNode::accept(Visitor& v) {
  v(*this);
}


// ====== Reference node


smtAstReferenceNode::smtAstReferenceNode(uint64 value) {
  this->kind  = REFERENCE_NODE;
  this->value = value;
}


smtAstReferenceNode::smtAstReferenceNode(const smtAstReferenceNode &copy) {
  this->kind  = copy.kind;
  this->value = copy.value;
}


smtAstReferenceNode::~smtAstReferenceNode() {
  freeAllNodes(this->childs);
}


uint64 smtAstReferenceNode::getValue(void) {
  return this->value;
}

void smtAstReferenceNode::accept(Visitor& v) {
  v(*this);
}


// ====== String node


smtAstStringNode::smtAstStringNode(std::string value) {
  this->kind  = STRING_NODE;
  this->value = value;
}


smtAstStringNode::smtAstStringNode(const smtAstStringNode &copy) {
  this->kind  = copy.kind;
  this->value = copy.value;
}


smtAstStringNode::~smtAstStringNode() {
  freeAllNodes(this->childs);
}


std::string smtAstStringNode::getValue(void) {
  return this->value;
}


void smtAstStringNode::accept(Visitor& v) {
  v(*this);
}


// ====== sx


smtAstSxNode::smtAstSxNode(uint64 sizeExt, smtAstAbstractNode *expr) {
  this->kind = SX_NODE;
  this->addChild(new smtAstDecimalNode(sizeExt));
  this->addChild(expr);
}


smtAstSxNode::smtAstSxNode(const smtAstSxNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstSxNode::~smtAstSxNode() {
  freeAllNodes(this->childs);
}

void smtAstSxNode::accept(Visitor& v) {
  v(*this);
}


// ====== Variable node


smtAstVariableNode::smtAstVariableNode(std::string variable) {
  this->kind  = VARIABLE_NODE;
  this->value = variable;
}


smtAstVariableNode::smtAstVariableNode(const smtAstVariableNode &copy) {
  this->kind  = copy.kind;
  this->value = copy.value;
}


smtAstVariableNode::~smtAstVariableNode() {
  freeAllNodes(this->childs);
}


std::string smtAstVariableNode::getValue(void) {
  return this->value;
}


void smtAstVariableNode::accept(Visitor& v) {
  v(*this);
}


// ====== zx


smtAstZxNode::smtAstZxNode(uint64 sizeExt, smtAstAbstractNode *expr) {
  this->kind = ZX_NODE;
  this->addChild(new smtAstDecimalNode(sizeExt));
  this->addChild(expr);
}


smtAstZxNode::smtAstZxNode(const smtAstZxNode &copy) {
  this->kind = copy.kind;
  for (uint64 index = 0; index < copy.childs.size(); index++)
    this->childs.push_back(newInstance(copy.childs[index]));
}


smtAstZxNode::~smtAstZxNode() {
  freeAllNodes(this->childs);
}

void smtAstZxNode::accept(Visitor& v) {
  v(*this);
}


// ====== Operators


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
      case REFERENCE_NODE:  stream << reinterpret_cast<smtAstReferenceNode *>(node); break;
      case STRING_NODE:     stream << reinterpret_cast<smtAstStringNode *>(node); break;
      case SX_NODE:         stream << reinterpret_cast<smtAstSxNode *>(node); break;
      case VARIABLE_NODE:   stream << reinterpret_cast<smtAstVariableNode *>(node); break;
      case ZX_NODE:         stream << reinterpret_cast<smtAstZxNode *>(node); break;
      default:
        throw std::invalid_argument("smt2lib::operator<<(smtAstAbstractNode) - Invalid kind node");
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


  /* bvnor syntax */
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
    uint64 index = 0;
    for ( ; index < node->getChilds().size(); index++)
      stream << node->getChilds()[index];
    return stream;
  }


  /* concat syntax */
  std::ostream &operator<<(std::ostream &stream, smtAstConcatNode *node) {

    uint64 index;
    std::vector<smtAstAbstractNode *> childs = node->getChilds();
    uint64 size = childs.size();

    if (size < 2)
      throw std::length_error("smtAstConcatNode - exprs must contain at less two expressions");

    stream << "(concat";
    for (index = 0; index < size; index++)
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

}


// ====== Utils


namespace smt2lib {

  /* Free all childs node */
  void freeAllNodes(std::vector<smtAstAbstractNode *> &childs) {
    //uint64 index = 0;
    // TODO - FIXME: #141
    //while (index < childs.size()) {
    //  delete childs[index];
    //  index++;
    //}
    childs.clear();
  }

}


// ====== Node builders


namespace smt2lib {

  smtAstAbstractNode *smtAssert(smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstAssertNode(expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bv(uint128 value, uint64 size) {
    smtAstAbstractNode *node = new smtAstBvNode(value, size);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvadd(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvaddNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvand(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvandNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvashr(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvashrNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvfalse(void) {
    smtAstAbstractNode *node = new smtAstBvNode(0, 1);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvlshr(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvlshrNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvmul(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvmulNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvnand(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvnandNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvneg(smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstBvnegNode(expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvnor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvnorNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvnot(smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstBvnotNode(expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvorNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvrol(uint64 rot, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstBvrolNode(rot, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvrol(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstBvrolNode(rot, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvror(uint64 rot, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstBvrorNode(rot, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvror(smtAstAbstractNode *rot, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstBvrorNode(rot, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsdiv(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsdivNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsge(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsgeNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsgt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsgtNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvshl(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvshlNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsle(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsleNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvslt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsltNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsmod(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsmodNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsrem(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsremNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvsub(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvsubNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvtrue(void) {
    smtAstAbstractNode *node = new smtAstBvNode(1, 1);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvudiv(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvudivNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvuge(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvugeNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvugt(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvugtNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvule(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvuleNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvult(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvultNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvurem(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvuremNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvxnor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvxnorNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *bvxor(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstBvxorNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *compound(std::vector<smtAstAbstractNode*> exprs) {
    smtAstAbstractNode *node = new smtAstCompoundNode(exprs);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *concat(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstConcatNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *concat(std::vector<smtAstAbstractNode *> exprs) {
    smtAstAbstractNode *node = new smtAstConcatNode(exprs);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *concat(std::list<smtAstAbstractNode *> exprs) {
    smtAstAbstractNode *node = new smtAstConcatNode(exprs);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *decimal(uint128 value) {
    smtAstAbstractNode *node = new smtAstDecimalNode(value);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *declare(std::string symVarName, uint64 symVarSize) {
    smtAstAbstractNode *node = new smtAstDeclareNode(symVarName, symVarSize);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }

  smtAstAbstractNode *distinct(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstDistinctNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *equal(smtAstAbstractNode *expr1, smtAstAbstractNode *expr2) {
    smtAstAbstractNode *node = new smtAstEqualNode(expr1, expr2);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *extract(uint64 high, uint64 low, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstExtractNode(high, low, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *ite(smtAstAbstractNode *ifExpr, smtAstAbstractNode *thenExpr, smtAstAbstractNode *elseExpr) {
    smtAstAbstractNode *node = new smtAstIteNode(ifExpr, thenExpr, elseExpr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *reference(uint64 value) {
    smtAstAbstractNode *node = new smtAstReferenceNode(value);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *string(std::string value) {
    smtAstAbstractNode *node = new smtAstStringNode(value);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *sx(uint64 sizeExt, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstSxNode(sizeExt, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *variable(std::string value) {
    smtAstAbstractNode *node = new smtAstVariableNode(value);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
  }


  smtAstAbstractNode *zx(uint64 sizeExt, smtAstAbstractNode *expr) {
    smtAstAbstractNode *node = new smtAstZxNode(sizeExt, expr);
    if (node == nullptr)
      throw std::runtime_error("Node builders - Not enough memory");
    return node;
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
      case REFERENCE_NODE:  newNode = new smtAstReferenceNode(*reinterpret_cast<smtAstReferenceNode *>(node)); break;
      case STRING_NODE:     newNode = new smtAstStringNode(*reinterpret_cast<smtAstStringNode *>(node)); break;
      case SX_NODE:         newNode = new smtAstSxNode(*reinterpret_cast<smtAstSxNode *>(node)); break;
      case VARIABLE_NODE:   newNode = new smtAstVariableNode(*reinterpret_cast<smtAstVariableNode *>(node)); break;
      case ZX_NODE:         newNode = new smtAstZxNode(*reinterpret_cast<smtAstZxNode *>(node)); break;
      default:
        throw std::invalid_argument("smt2lib::newInstance() - Invalid kind node");
    }
    return newNode;
  }

}

#endif /* LIGHT_VERSION */

