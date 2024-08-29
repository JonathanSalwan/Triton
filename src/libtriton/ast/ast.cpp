//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <algorithm>
#include <cmath>
#include <list>
#include <new>
#include <stack>
#include <unordered_map>
#include <unordered_set>
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

    AbstractNode::AbstractNode(triton::ast::ast_e type, const SharedAstContext& ctxt) {
      this->array       = false;
      this->ctxt        = ctxt;
      this->eval        = 0;
      this->hash        = 0;
      this->logical     = false;
      this->level       = 1;
      this->size        = 0;
      this->symbolized  = false;
      this->type        = type;
    }


    AbstractNode::~AbstractNode() {
      /* See #828: Release ownership before calling container destructor */
      this->children.clear();
    }


    SharedAstContext AbstractNode::getContext(void) const {
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
        case FORALL_NODE:
        case IFF_NODE:
        case LAND_NODE:
        case LNOT_NODE:
        case LOR_NODE:
        case LXOR_NODE:
          return true;

        case ITE_NODE:
        case REFERENCE_NODE:
          return this->logical;

        default:
          break;
      }

      return false;
    }


    bool AbstractNode::isArray(void) const {
      switch (this->type) {
        case ARRAY_NODE:
        case STORE_NODE:
          return true;

        /*
         * Note that SELECT is not a node of type Array. SELECT returns
         * a node of type (_ BitVec 8).
         */

        case REFERENCE_NODE:
          return this->array;

        default:
          break;
      }

      return false;
    }


    bool AbstractNode::hasSameConcreteValueAndTypeAs(const SharedAbstractNode& other) const {
      return (this->evaluate() == other->evaluate()) &&
             (this->getBitvectorSize() == other->getBitvectorSize()) &&
             (this->isLogical() == other->isLogical());
    }


    bool AbstractNode::canReplaceNodeWithoutUpdate(const SharedAbstractNode& other) const {
      return (this->hasSameConcreteValueAndTypeAs(other)) &&
             (this->isSymbolized() == other->isSymbolized());
    }


    bool AbstractNode::equalTo(const SharedAbstractNode& other) const {
      return (this->evaluate() == other->evaluate()) &&
             (this->getBitvectorSize() == other->getBitvectorSize()) &&
             (this->getHash() == other->getHash()) &&
             (this->getLevel() == other->getLevel());
    }


    triton::uint512 AbstractNode::evaluate(void) const {
      return this->eval;
    }


    triton::uint512 AbstractNode::getHash(void) const {
      return this->hash;
    }


    triton::uint32 AbstractNode::getLevel(void) const {
      return this->level;
    }


    void AbstractNode::initParents(void) {
      auto ancestors = parentsExtraction(this->shared_from_this(), false);
      for (auto& sp : ancestors) {
        sp->init();
      }
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
        SharedAbstractNode A = p->shared_from_this();
        this->parents.insert(std::make_pair(p, std::make_pair(1, WeakAbstractNode(A))));
      }
      else {
        if (it->second.second.expired()) {
          parents.erase(it);
          SharedAbstractNode A = p->shared_from_this();
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

      if (it == parents.end())
        return;

      it->second.first--;
      if (it->second.first == 0)
        this->parents.erase(it);
    }


    void AbstractNode::setParent(std::unordered_set<AbstractNode*>& p) {
      for (AbstractNode* ptr : p) {
        this->setParent(ptr);
      }
    }


    void AbstractNode::addChild(const SharedAbstractNode& child) {
      this->children.push_back(child);
    }


    void AbstractNode::setChild(triton::uint32 index, const SharedAbstractNode& child) {
      if (index >= this->children.size())
        throw triton::exceptions::Ast("AbstractNode::setChild(): Invalid index.");

      if (child == nullptr)
        throw triton::exceptions::Ast("AbstractNode::setChild(): child cannot be null.");

      if (this->children[index] != child) {
        /* Remove the parent of the old child */
        this->children[index]->removeParent(this);

        /* Setup the parent of the child */
        child->setParent(this);

        /* Setup the child of the parent */
        this->children[index] = child;

        /* Init parents */
        child->initParents();
      }
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


    /* ====== array */


    ArrayNode::ArrayNode(triton::uint32 indexSize, const SharedAstContext& ctxt): AbstractNode(ARRAY_NODE, ctxt) {
      this->indexSize = indexSize;
      this->addChild(this->ctxt->integer(indexSize));
    }


    void ArrayNode::init(bool withParents) {
      /* Init attributes. */
      this->size       = 0; // Array do not have size.
      this->eval       = 0; // Array cannot be evaluated.
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void ArrayNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    void ArrayNode::store(triton::uint64 addr, triton::uint8 value) {
      this->memory[addr] = value;
    }


    triton::uint8 ArrayNode::select(triton::uint64 addr) const {
      if (this->memory.find(addr) != this->memory.end()) {
        return this->memory.at(addr);
      }
      return 0;
    }


    triton::uint8 ArrayNode::select(const triton::uint512& addr) const {
      return this->select(static_cast<triton::uint64>(addr));
    }


    triton::uint8 ArrayNode::select(const SharedAbstractNode& node) const {
      return this->select(static_cast<triton::uint64>(node->evaluate()));
    }


    std::unordered_map<triton::uint64, triton::uint8>& ArrayNode::getMemory(void) {
      return this->memory;
    }


    triton::uint32 ArrayNode::getIndexSize(void) const {
      return this->indexSize;
    }


    /* ====== assert */


    AssertNode::AssertNode(const SharedAbstractNode& expr): AbstractNode(ASSERT_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void AssertNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("AssertNode::init(): Must take at least one child.");

      if (this->children[0]->isLogical() == false)
        throw triton::exceptions::Ast("AssertNode::init(): Must take a logical node as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = ((this->children[0]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void AssertNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bswap */


    BswapNode::BswapNode(const SharedAbstractNode& expr): AbstractNode(BSWAP_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void BswapNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("BswapNode::init(): Must take at least one child.");

      if (this->children[0]->getBitvectorSize() % 8 != 0)
        throw triton::exceptions::Ast("BswapNode::init(): Invalid size, must be aligned on 8-bit.");

      if (this->children[0]->isArray())
        throw triton::exceptions::Ast("BswapNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = this->children[0]->evaluate() & 0xff;
      this->level      = 1;
      this->symbolized = false;

      /* Init eval */
      for (triton::uint32 index = 8 ; index != this->size ; index += triton::bitsize::byte) {
        this->eval <<= triton::bitsize::byte;
        this->eval |= ((this->children[0]->evaluate() >> index) & 0xff);
      }

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BswapNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvadd */


    BvaddNode::BvaddNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVADD_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvaddNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvaddNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvaddNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvaddNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = ((this->children[0]->evaluate() + this->children[1]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvaddNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvand */


    BvandNode::BvandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvandNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvandNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvandNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvandNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (this->children[0]->evaluate() & this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvandNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvashr (shift with sign extension fill) */


    BvashrNode::BvashrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVASHR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvashrNode::init(bool withParents) {
      triton::uint32 shift  = 0;
      triton::uint512 mask  = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvashrNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvashrNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvashrNode::init(): Cannot take an array as argument.");

      value = this->children[0]->evaluate();
      shift = static_cast<triton::uint32>(this->children[1]->evaluate());

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->level      = 1;
      this->symbolized = false;

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
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvashrNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvlshr (shift with zero filled) */


    BvlshrNode::BvlshrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVLSHR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvlshrNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvlshrNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvlshrNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvlshrNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (this->children[0]->evaluate() >> static_cast<triton::uint32>(this->children[1]->evaluate()));
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvlshrNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvmul */


    BvmulNode::BvmulNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVMUL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvmulNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvmulNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvmulNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvmulNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = ((this->children[0]->evaluate() * this->children[1]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvmulNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvnand */


    BvnandNode::BvnandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVNAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvnandNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvnandNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvnandNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvnandNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (~(this->children[0]->evaluate() & this->children[1]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvnandNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvneg */


    BvnegNode::BvnegNode(const SharedAbstractNode& expr): AbstractNode(BVNEG_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void BvnegNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("BvnegNode::init(): Must take at least one child.");

      if (this->children[0]->isArray())
        throw triton::exceptions::Ast("BvnegNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (static_cast<triton::uint512>((-(static_cast<triton::sint512>(this->children[0]->evaluate())))) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvnegNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvnor */


    BvnorNode::BvnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVNOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvnorNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvnorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvnorNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvnorNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (~(this->children[0]->evaluate() | this->children[1]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvnorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvnot */


    BvnotNode::BvnotNode(const SharedAbstractNode& expr): AbstractNode(BVNOT_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void BvnotNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("BvnotNode::init(): Must take at least one child.");

      if (this->children[0]->isArray())
        throw triton::exceptions::Ast("BvnotNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (~this->children[0]->evaluate() & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvnotNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvor */


    BvorNode::BvorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvorNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[0]->getBitvectorSize())
        throw triton::exceptions::Ast("BvorNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvorNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (this->children[0]->evaluate() | this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvrol */


    BvrolNode::BvrolNode(const SharedAbstractNode& expr, triton::uint32 rot): BvrolNode(expr, expr->getContext()->integer(rot)) {
    }


    BvrolNode::BvrolNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot): AbstractNode(BVROL_NODE, expr->getContext()) {
      this->addChild(expr);
      this->addChild(rot);
    }


    void BvrolNode::init(bool withParents) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvrolNode::init(): Must take at least two children.");

      if (this->children[0]->isArray())
        throw triton::exceptions::Ast("BvrolNode::init(): Cannot take an array as argument.");

      rot   = triton::ast::getInteger<triton::uint32>(this->children[1]);
      value = this->children[0]->evaluate();

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      rot             %= this->size;
      this->eval       = (((value << rot) | (value >> (this->size - rot))) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvrolNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvror */


    BvrorNode::BvrorNode(const SharedAbstractNode& expr, triton::uint32 rot): BvrorNode(expr, expr->getContext()->integer(rot)) {
    }


    BvrorNode::BvrorNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot): AbstractNode(BVROR_NODE, expr->getContext()) {
      this->addChild(expr);
      this->addChild(rot);
    }


    void BvrorNode::init(bool withParents) {
      triton::uint32 rot    = 0;
      triton::uint512 value = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvrorNode::init(): Must take at least two children.");

      if (this->children[0]->isArray())
        throw triton::exceptions::Ast("BvrorNode::init(): Cannot take an array as argument.");

      rot   = triton::ast::getInteger<triton::uint32>(this->children[1]);
      value = this->children[0]->evaluate();

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      rot             %= this->size;
      this->eval       = (((value >> rot) | (value << (this->size - rot))) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvrorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsdiv */


    BvsdivNode::BvsdivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSDIV_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsdivNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsdivNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsdivNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->level      = 1;
      this->symbolized = false;

      if (op2Signed == 0) {
        this->eval = (op1Signed < 0 ? 1 : -1);
        this->eval &= this->getBitvectorMask();
      }
      else
        this->eval = (static_cast<triton::uint512>((op1Signed / op2Signed)) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsdivNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsge */


    BvsgeNode::BvsgeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSGE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsgeNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgeNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsgeNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = 1;
      this->eval       = (op1Signed >= op2Signed);
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsgeNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsgt */


    BvsgtNode::BvsgtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSGT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsgtNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsgtNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsgtNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = 1;
      this->eval       = (op1Signed > op2Signed);
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsgtNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvshl */


    BvshlNode::BvshlNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSHL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvshlNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvshlNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvshlNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvshlNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = ((this->children[0]->evaluate() << static_cast<triton::uint32>(this->children[1]->evaluate())) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvshlNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsle */


    BvsleNode::BvsleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSLE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsleNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsleNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsleNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = 1;
      this->eval       = (op1Signed <= op2Signed);
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsleNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvslt */


    BvsltNode::BvsltNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSLT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsltNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsltNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsltNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsltNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = 1;
      this->eval       = (op1Signed < op2Signed);
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsltNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsmod - 2's complement signed remainder (sign follows divisor) */


    BvsmodNode::BvsmodNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSMOD_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsmodNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsmodNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsmodNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->level      = 1;
      this->symbolized = false;

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = (static_cast<triton::uint512>((((op1Signed % op2Signed) + op2Signed) % op2Signed)) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsmodNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsrem - 2's complement signed remainder (sign follows dividend) */


    BvsremNode::BvsremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSREM_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsremNode::init(bool withParents) {
      triton::sint512 op1Signed = 0;
      triton::sint512 op2Signed = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsremNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsremNode::init(): Cannot take an array as argument.");

      /* Sign extend */
      op1Signed = triton::ast::modularSignExtend(this->children[0].get());
      op2Signed = triton::ast::modularSignExtend(this->children[1].get());

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->level      = 1;
      this->symbolized = false;

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = (static_cast<triton::uint512>((op1Signed - ((op1Signed / op2Signed) * op2Signed))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsremNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvsub */


    BvsubNode::BvsubNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVSUB_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvsubNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvsubNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvsubNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvsubNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = ((this->children[0]->evaluate() - this->children[1]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvsubNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvudiv */


    BvudivNode::BvudivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUDIV_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvudivNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvudivNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvudivNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvudivNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->level      = 1;
      this->symbolized = false;

      if (this->children[1]->evaluate() == 0)
        this->eval = (-1 & this->getBitvectorMask());
      else
        this->eval = (this->children[0]->evaluate() / this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvudivNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvuge */


    BvugeNode::BvugeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUGE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvugeNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvugeNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvugeNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvugeNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = (this->children[0]->evaluate() >= this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvugeNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvugt */


    BvugtNode::BvugtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUGT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvugtNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvugtNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvugtNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvugtNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = (this->children[0]->evaluate() > this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvugtNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvule */


    BvuleNode::BvuleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVULE_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvuleNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvuleNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvuleNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvuleNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = (this->children[0]->evaluate() <= this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvuleNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvult */


    BvultNode::BvultNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVULT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvultNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvultNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvultNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvultNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = (this->children[0]->evaluate() < this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvultNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvurem */


    BvuremNode::BvuremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVUREM_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvuremNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvuremNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvuremNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvuremNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->level      = 1;
      this->symbolized = false;

      if (this->children[1]->evaluate() == 0)
        this->eval = this->children[0]->evaluate();
      else
        this->eval = (this->children[0]->evaluate() % this->children[1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvuremNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvxnor */


    BvxnorNode::BvxnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVXNOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvxnorNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvxnorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvxnorNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvxnorNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (~(this->children[0]->evaluate() ^ this->children[1]->evaluate()) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvxnorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bvxor */


    BvxorNode::BvxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(BVXOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void BvxorNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvxorNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("BvxorNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("BvxorNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = (this->children[0]->evaluate() ^ this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvxorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== bv */


    BvNode::BvNode(const triton::uint512& value, triton::uint32 size, const SharedAstContext& ctxt): AbstractNode(BV_NODE, ctxt) {
      this->size = size;
      this->addChild(this->ctxt->integer(value & this->getBitvectorMask()));
      this->addChild(this->ctxt->integer(size));
    }


    void BvNode::init(bool withParents) {
      triton::uint512 value = 0;
      triton::uint32 size   = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("BvNode::init(): Must take at least two children.");

      value = triton::ast::getInteger<triton::uint512>(this->children[0]);
      size  = triton::ast::getInteger<triton::uint32>(this->children[1]);

      if (!size)
        throw triton::exceptions::Ast("BvNode::init(): Size cannot be equal to zero.");

      if (size > triton::bitsize::max_supported)
        throw triton::exceptions::Ast("BvNode::init(): Size cannot be greater than triton::bitsize::max_supported.");

      /* Init attributes */
      this->size       = size;
      this->eval       = (value & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void BvNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== compound */


    void CompoundNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("CompoundNode::init(): Must take at least one child.");

      /* Init attributes */
      this->eval       = 0;
      this->size       = 0;
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void CompoundNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== concat */


    ConcatNode::ConcatNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(CONCAT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void ConcatNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("ConcatNode::init(): Must take at least two children.");

      /* Init attributes */
      this->level      = 1;
      this->symbolized = false;
      this->size       = 0;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->size += this->children[index]->getBitvectorSize();
      }

      if (this->size > triton::bitsize::max_supported)
        throw triton::exceptions::Ast("ConcatNode::init(): Size cannot be greater than triton::bitsize::max_supported.");

      this->eval = this->children[0]->evaluate();
      for (triton::uint32 index = 0; index < this->children.size()-1; index++)
        this->eval = ((this->eval << this->children[index+1]->getBitvectorSize()) | this->children[index+1]->evaluate());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        if (this->children[index]->isArray()) {
          throw triton::exceptions::Ast("ConcatNode::init(): Cannot take an array as argument.");
        }
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void ConcatNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Declare */


    DeclareNode::DeclareNode(const SharedAbstractNode& var): AbstractNode(DECLARE_NODE, var->getContext()) {
      this->addChild(var);
    }


    void DeclareNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("DeclareNode::init(): Must take at least one child.");

      if (this->children[0]->getType() != VARIABLE_NODE && this->children[0]->getType() != ARRAY_NODE)
        throw triton::exceptions::Ast("DeclareNode::init(): The child node must be a VARIABLE_NODE or an ARRAY_NODE.");

      /* Init attributes */
      this->size       = this->children[0]->getBitvectorSize();
      this->eval       = this->children[0]->evaluate();
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void DeclareNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Distinct node */


    DistinctNode::DistinctNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(DISTINCT_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void DistinctNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("DistinctNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("DistinctNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("DistinctNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = (this->children[0]->evaluate() != this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void DistinctNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== equal */


    EqualNode::EqualNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(EQUAL_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void EqualNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("EqualNode::init(): Must take at least two children.");

      if (this->children[0]->getBitvectorSize() != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("EqualNode::init(): Must take two nodes of same size.");

      if (this->children[0]->isArray() || this->children[1]->isArray())
        throw triton::exceptions::Ast("EqualNode::init(): Cannot take an array as argument.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = (this->children[0]->evaluate() == this->children[1]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void EqualNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== extract */


    ExtractNode::ExtractNode(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr): AbstractNode(EXTRACT_NODE, expr->getContext()) {
      this->addChild(this->ctxt->integer(high));
      this->addChild(this->ctxt->integer(low));
      this->addChild(expr);
    }


    void ExtractNode::init(bool withParents) {
      triton::uint32 high = 0;
      triton::uint32 low  = 0;

      if (this->children.size() < 3)
        throw triton::exceptions::Ast("ExtractNode::init(): Must take at least three children.");

      if (this->children[2]->isArray())
        throw triton::exceptions::Ast("ExtractNode::init(): Cannot take an array as argument.");

      high = triton::ast::getInteger<triton::uint32>(this->children[0]);
      low  = triton::ast::getInteger<triton::uint32>(this->children[1]);

      if (low > high)
        throw triton::exceptions::Ast("ExtractNode::init(): The high bit must be greater than the low bit.");

      /* Init attributes */
      this->size       = ((high - low) + 1);
      this->eval       = ((this->children[2]->evaluate() >> low) & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      if (this->size > this->children[2]->getBitvectorSize() || high >= this->children[2]->getBitvectorSize())
        throw triton::exceptions::Ast("ExtractNode::init(): The size of the extraction is higher than the child expression.");

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void ExtractNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== forall */


    void ForallNode::init(bool withParents) {
      triton::usize size = this->children.size();

      if (size < 2)
        throw triton::exceptions::Ast("ForallNode::init(): Must take at least two children.");

      for (triton::uint32 i = 0; i != size - 1; i++) {
        if (this->children[i]->getType() != VARIABLE_NODE)
          throw triton::exceptions::Ast("ForallNode::init(): Must take a variable node as first arguments.");
      }

      if (this->children[size - 1]->isLogical() == false)
        throw triton::exceptions::Ast("ForallNode::init(): Must take a logical node as body.");

      this->size       = 1;
      this->eval       = 0;
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void ForallNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== iff */


    IffNode::IffNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(IFF_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void IffNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("IffNode::init(): Must take at least two children.");

      if (this->children[0]->isLogical() == false)
        throw triton::exceptions::Ast("IffNode::init(): Must take a logical node as first argument.");

      if (this->children[1]->isLogical() == false)
        throw triton::exceptions::Ast("IffNode::init(): Must take a logical node as second argument.");

      /* Init attributes */
      triton::uint512 P = this->children[0]->evaluate();
      triton::uint512 Q = this->children[1]->evaluate();

      this->size       = 1;
      this->eval       = (P && Q) || (!P && !Q);
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void IffNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Integer node */


    IntegerNode::IntegerNode(const triton::uint512& value, const SharedAstContext& ctxt): AbstractNode(INTEGER_NODE, ctxt) {
      this->value = value;
    }


    void IntegerNode::init(bool withParents) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->level       = 1;
      this->symbolized  = false;

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    triton::uint512 IntegerNode::getInteger(void) {
      return this->value;
    }


    void IntegerNode::initHash(void) {
      static const triton::uint512 even_flag = (triton::uint512(1) << 64) | 1;
      if ((this->value & 1) == 0) {
        this->hash = static_cast<triton::uint64>(this->type) ^ this->value;
      } else {
        this->hash = static_cast<triton::uint64>(this->type) ^ this->value ^ (even_flag);
      }
    }


    /* ====== ite */


    IteNode::IteNode(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr): AbstractNode(ITE_NODE, ifExpr->getContext()) {
      this->addChild(ifExpr);
      this->addChild(thenExpr);
      this->addChild(elseExpr);
    }


    void IteNode::init(bool withParents) {
      if (this->children.size() < 3)
        throw triton::exceptions::Ast("IteNode::init(): Must take at least three children.");

      if (this->children[0]->isLogical() == false)
        throw triton::exceptions::Ast("IteNode::init(): Must take a logical node as first argument.");

      if (this->children[1]->getBitvectorSize() != this->children[2]->getBitvectorSize())
        throw triton::exceptions::Ast("IteNode::init(): Must take two nodes of same size as 'then' and 'else' branches.");

      if (this->children[1]->isArray() || this->children[2]->isArray())
        throw triton::exceptions::Ast("IteNode::init(): Cannot take an array as argument.");

      if (this->children[1]->isLogical() != this->children[2]->isLogical())
        throw triton::exceptions::Ast("IteNode::init(): Must take either two logical nodes or two bv nodes as 'then' and 'else' branches.");

      /* Init attributes */
      this->size       = this->children[1]->getBitvectorSize();
      this->eval       = this->children[0]->evaluate() ? this->children[1]->evaluate() : this->children[2]->evaluate();
      this->logical    = this->children[1]->isLogical();
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Spread symbolic information */
      if (!this->children[0]->isSymbolized()) {
        this->symbolized = this->children[0]->evaluate() ? this->children[1]->isSymbolized() : this->children[2]->isSymbolized();
      } else {
        this->symbolized = true;
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void IteNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Land */


    LandNode::LandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(LAND_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void LandNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("LandNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = 1;
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        if (this->children[index]->isLogical() == false) {
          throw triton::exceptions::Ast("LandNode::init(): Must take logical nodes as arguments.");
        }
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = this->eval && this->children[index]->evaluate();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void LandNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Let */


    LetNode::LetNode(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3): AbstractNode(LET_NODE, expr2->getContext()) {
      this->addChild(this->ctxt->string(alias));
      this->addChild(expr2);
      this->addChild(expr3);
    }


    void LetNode::init(bool withParents) {
      if (this->children.size() < 3)
        throw triton::exceptions::Ast("LetNode::init(): Must take at least three children.");

      if (this->children[0]->getType() != STRING_NODE)
        throw triton::exceptions::Ast("LetNode::init(): The alias node must be a STRING_NODE.");

      /* Init attributes */
      this->size       = this->children[2]->getBitvectorSize();
      this->eval       = this->children[2]->evaluate();
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void LetNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Lnot */


    LnotNode::LnotNode(const SharedAbstractNode& expr): AbstractNode(LNOT_NODE, expr->getContext()) {
      this->addChild(expr);
    }


    void LnotNode::init(bool withParents) {
      if (this->children.size() < 1)
        throw triton::exceptions::Ast("LnotNode::init(): Must take at least one child.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = !(this->children[0]->evaluate());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        if (this->children[index]->isLogical() == false) {
          throw triton::exceptions::Ast("LnotNode::init(): Must take logical nodes arguments.");
        }
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void LnotNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Lor */


    LorNode::LorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2): AbstractNode(LOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void LorNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("LorNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = 0;
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        if (this->children[index]->isLogical() == false) {
          throw triton::exceptions::Ast("LorNode::init(): Must take logical nodes as arguments.");
        }
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = this->eval || this->children[index]->evaluate();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void LorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Lxor */


    LxorNode::LxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2) : AbstractNode(LXOR_NODE, expr1->getContext()) {
      this->addChild(expr1);
      this->addChild(expr2);
    }


    void LxorNode::init(bool withParents) {
      if (this->children.size() < 2)
        throw triton::exceptions::Ast("LxorNode::init(): Must take at least two children.");

      /* Init attributes */
      this->size       = 1;
      this->eval       = 0;
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        if (this->children[index]->isLogical() == false) {
          throw triton::exceptions::Ast("LxorNode::init(): Must take logical nodes as arguments.");
        }
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->eval = !this->eval != !this->children[index]->evaluate();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void LxorNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Reference node */


    ReferenceNode::ReferenceNode(const triton::engines::symbolic::SharedSymbolicExpression& expr)
      : AbstractNode(REFERENCE_NODE, expr->getAst()->getContext())
      , expr(expr) {
        this->addChild(expr->getAst());
    }


    void ReferenceNode::init(bool withParents) {
      /* Init attributes */
      this->array       = this->expr->getAst()->isArray();
      this->eval        = this->expr->getAst()->evaluate();
      this->logical     = this->expr->getAst()->isLogical();
      this->size        = this->expr->getAst()->getBitvectorSize();
      this->symbolized  = this->expr->getAst()->isSymbolized();
      this->level       = 1 + this->expr->getAst()->getLevel();

      this->expr->getAst()->setParent(this);

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void ReferenceNode::initHash(void) {
      this->hash = this->expr->getAst()->getHash();
    }


    const triton::engines::symbolic::SharedSymbolicExpression& ReferenceNode::getSymbolicExpression(void) const {
      return this->expr;
    }


    /* ====== Select node */

    SelectNode::SelectNode(const SharedAbstractNode& array, triton::usize index): AbstractNode(SELECT_NODE, array->getContext()) {
      this->addChild(array);
      this->addChild(this->ctxt->bv(index, triton::ast::getIndexSize(array)));
    }


    SelectNode::SelectNode(const SharedAbstractNode& array, const SharedAbstractNode& index): AbstractNode(SELECT_NODE, array->getContext()) {
      this->addChild(array);
      this->addChild(index);
    }


    void SelectNode::init(bool withParents) {
      if (this->children.size() != 2)
        throw triton::exceptions::Ast("SelectNode::init(): Must take two children.");

      if (this->children[0]->isArray() == false)
        throw triton::exceptions::Ast("SelectNode::init(): Must take an array as first argument.");

      if (triton::ast::getIndexSize(this->children[0]) != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("SelectNode::init(): Size of indexing must be equal.");

      /* Init attributes */
      this->size       = 8; /* Size of a memory cell */
      this->level      = 1;
      this->symbolized = false;

      auto node = triton::ast::dereference(this->children[0]);
      switch(node->getType()) {
        case ARRAY_NODE:
          this->eval = reinterpret_cast<ArrayNode*>(node.get())->select(this->children[1]);
          break;
        case STORE_NODE:
          this->eval = reinterpret_cast<StoreNode*>(node.get())->select(this->children[1]);
          break;
        default:
          throw triton::exceptions::Ast("SelectNode::init(): Invalid sort");
      }

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void  SelectNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Store node */


    StoreNode::StoreNode(const SharedAbstractNode& array, triton::usize index, const SharedAbstractNode& expr): AbstractNode(STORE_NODE, array->getContext()) {
      this->addChild(array);
      this->addChild(this->ctxt->bv(index, triton::ast::getIndexSize(array)));
      this->addChild(expr);
    }


    StoreNode::StoreNode(const SharedAbstractNode& array, const SharedAbstractNode& index, const SharedAbstractNode& expr): AbstractNode(STORE_NODE, array->getContext()) {
      this->addChild(array);
      this->addChild(index);
      this->addChild(expr);
    }


    void StoreNode::init(bool withParents) {
      if (this->children.size() != 3)
        throw triton::exceptions::Ast("StoreNode::init(): Must take three children.");

      if (this->children[0]->isArray() == false)
        throw triton::exceptions::Ast("StoreNode::init(): Must take an array as first argument.");

      if (triton::ast::getIndexSize(this->children[0]) != this->children[1]->getBitvectorSize())
        throw triton::exceptions::Ast("StoreNode::init(): Size of indexing must be equal to the array indexing size.");

      if (this->children[2]->getBitvectorSize() != triton::bitsize::byte)
        throw triton::exceptions::Ast("StoreNode::init(): The stored node must be 8-bit long");

      /* Init attributes */
      this->eval       = this->children[2]->evaluate();
      this->size       = 0; // Array do not have size.
      this->level      = 1;
      this->symbolized = false;

      /* Spread the memory array from previous level */
      auto node = triton::ast::dereference(this->children[0]);
      switch(node->getType()) {
        case ARRAY_NODE:
          this->indexSize = reinterpret_cast<ArrayNode*>(node.get())->getIndexSize();
          this->memory    = reinterpret_cast<ArrayNode*>(node.get())->getMemory();
          break;
        case STORE_NODE:
          this->indexSize = reinterpret_cast<StoreNode*>(node.get())->getIndexSize();
          this->memory    = reinterpret_cast<StoreNode*>(node.get())->getMemory();
          break;
        default:
          throw triton::exceptions::Ast("StoreNode::init(): Invalid sort");
      }

      /* Store the value to the memory array */
      this->memory[static_cast<triton::uint64>(this->children[1]->evaluate())] = static_cast<triton::uint8>(this->eval);

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void StoreNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * this->children[index]->getHash();
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    triton::uint8 StoreNode::select(triton::uint64 addr) const {
      if (this->memory.find(addr) != this->memory.end()) {
        return this->memory.at(addr);
      }
      return 0;
    }


    triton::uint8 StoreNode::select(const triton::uint512& addr) const {
      return this->select(static_cast<triton::uint64>(addr));
    }


    triton::uint8 StoreNode::select(const SharedAbstractNode& node) const {
      return this->select(static_cast<triton::uint64>(node->evaluate()));
    }


    std::unordered_map<triton::uint64, triton::uint8>& StoreNode::getMemory(void) {
      return this->memory;
    }


    triton::uint32 StoreNode::getIndexSize(void) const {
      return this->indexSize;
    }


    /* ====== String node */


    StringNode::StringNode(std::string value, const SharedAstContext& ctxt): AbstractNode(STRING_NODE, ctxt) {
      this->value = value;
    }


    void StringNode::init(bool withParents) {
      /* Init attributes */
      this->eval        = 0;
      this->size        = 0;
      this->level       = 1;
      this->symbolized  = false;

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    std::string StringNode::getString(void) {
      return this->value;
    }


    void StringNode::initHash(void) {
      triton::uint32 index = 1;

      this->hash = static_cast<triton::uint64>(this->type);
      for (std::string::const_iterator it=this->value.cbegin(); it != this->value.cend(); it++) {
        this->hash = triton::ast::rotl(*it ^ this->hash ^ triton::ast::hash2n(this->hash, index++), *it);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== sx */


    SxNode::SxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr): AbstractNode(SX_NODE, expr->getContext()) {
      this->addChild(this->ctxt->integer(sizeExt));
      this->addChild(expr);
    }


    void SxNode::init(bool withParents) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("SxNode::init(): Must take at least two children.");

      if (this->children[1]->isArray())
        throw triton::exceptions::Ast("SxNode::init(): Cannot take an array as argument.");

      sizeExt = triton::ast::getInteger<triton::uint32>(this->children[0]);

      /* Init attributes */
      this->size = sizeExt + this->children[1]->getBitvectorSize();
      if (size > triton::bitsize::max_supported)
        throw triton::exceptions::Ast("SxNode::SxNode(): Size cannot be greater than triton::bitsize::max_supported.");

      this->level      = 1;
      this->symbolized = false;
      this->eval       = ((((this->children[1]->evaluate() >> (this->children[1]->getBitvectorSize()-1)) == 0) ?
                          this->children[1]->evaluate() : (this->children[1]->evaluate() | ~(this->children[1]->getBitvectorMask()))) & this->getBitvectorMask());

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void SxNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== Variable node */


    VariableNode::VariableNode(const triton::engines::symbolic::SharedSymbolicVariable& symVar, const SharedAstContext& ctxt)
      : AbstractNode(VARIABLE_NODE, ctxt),
        symVar(symVar) {
    }


    void VariableNode::init(bool withParents) {
      this->size        = this->symVar->getSize();
      this->eval        = this->ctxt->getVariableValue(this->symVar->getName()) & this->getBitvectorMask();
      this->symbolized  = true;
      this->level       = 1;

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    const triton::engines::symbolic::SharedSymbolicVariable& VariableNode::getSymbolicVariable() {
      return this->symVar;
    }


    void VariableNode::initHash(void) {
      triton::uint32 index = 1;
      triton::usize  id    = this->symVar->getId();

      this->hash = static_cast<triton::uint64>(this->type);
      for (char c : this->symVar->getName()) {
        this->hash = triton::ast::rotl(c ^ this->hash ^ triton::ast::hash2n(this->hash, index++), (id & 511));
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }


    /* ====== zx */


    ZxNode::ZxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr): AbstractNode(ZX_NODE, expr->getContext()) {
      this->addChild(this->ctxt->integer(sizeExt));
      this->addChild(expr);
    }


    void ZxNode::init(bool withParents) {
      triton::uint32 sizeExt = 0;

      if (this->children.size() < 2)
        throw triton::exceptions::Ast("ZxNode::init(): Must take at least two children.");

      if (this->children[1]->isArray())
        throw triton::exceptions::Ast("ZxNode::init(): Cannot take an array as argument.");

      sizeExt = triton::ast::getInteger<triton::uint32>(this->children[0]);

      /* Init attributes */
      this->size = sizeExt + this->children[1]->getBitvectorSize();
      if (size > triton::bitsize::max_supported)
        throw triton::exceptions::Ast("ZxNode::init(): Size cannot be greater than triton::bitsize::max_supported.");

      this->eval       = (this->children[1]->evaluate() & this->getBitvectorMask());
      this->level      = 1;
      this->symbolized = false;

      /* Init children and spread information */
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->children[index]->setParent(this);
        this->symbolized |= this->children[index]->isSymbolized();
        this->level = std::max(this->children[index]->getLevel() + 1, this->level);
      }

      /* Init parents if needed */
      if (withParents) {
        this->initParents();
      }

      this->initHash();
    }


    void ZxNode::initHash(void) {
      triton::uint512 s = this->children.size();

      this->hash = static_cast<triton::uint64>(this->type);
      if (s) this->hash = this->hash * s;
      for (triton::uint32 index = 0; index < this->children.size(); index++) {
        this->hash = this->hash * triton::ast::hash2n(this->children[index]->getHash(), index+1);
      }

      this->hash = triton::ast::rotl(this->hash, this->level);
    }

  }; /* ast namespace */
}; /* triton namespace */



/* ====== Force templates declarations */

namespace triton {
  namespace ast {

    template TRITON_EXPORT CompoundNode::CompoundNode(const std::list<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT CompoundNode::CompoundNode(const std::vector<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT ConcatNode::ConcatNode(const std::list<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT ConcatNode::ConcatNode(const std::vector<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT ForallNode::ForallNode(const std::list<SharedAbstractNode>& vars, const SharedAbstractNode& body);
    template TRITON_EXPORT ForallNode::ForallNode(const std::vector<SharedAbstractNode>& vars, const SharedAbstractNode& body);
    template TRITON_EXPORT LandNode::LandNode(const std::list<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT LandNode::LandNode(const std::vector<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT LorNode::LorNode(const std::list<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT LorNode::LorNode(const std::vector<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT LxorNode::LxorNode(const std::list<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);
    template TRITON_EXPORT LxorNode::LxorNode(const std::vector<SharedAbstractNode>& exprs, const SharedAstContext& ctxt);

  }; /* ast namespace */
}; /* triton namespace */



/* ====== Operators */

namespace triton {
  namespace ast {

    /* Representation dispatcher from an abstract node */
    std::ostream& operator<<(std::ostream& stream, AbstractNode* node) {
      return node->getContext()->print(stream, node);
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


    triton::uint512 rotl(const triton::uint512& value, triton::uint32 shift) {
      if ((shift &= 511) == 0)
        return value;
      return ((value << shift) | (value >> (512 - shift))) | 1;
    }


    triton::sint512 modularSignExtend(AbstractNode* node) {
      triton::sint512 value = 0;

      if ((node->evaluate() >> (node->getBitvectorSize()-1)) & 1) {
        value = -1;
        value = ((value << node->getBitvectorSize()) | static_cast<triton::sint512>(node->evaluate()));
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

    /* Returns a new instance of a given node. */
    static SharedAbstractNode shallowCopy(AbstractNode* node, bool unroll) {
      SharedAbstractNode newNode = nullptr;

      if (node == nullptr)
        throw triton::exceptions::Ast("triton::ast::shallowCopy(): node cannot be null.");

      switch (node->getType()) {
        case ARRAY_NODE:                newNode = std::make_shared<ArrayNode>(*reinterpret_cast<ArrayNode*>(node));       break;
        case ASSERT_NODE:               newNode = std::make_shared<AssertNode>(*reinterpret_cast<AssertNode*>(node));     break;
        case BSWAP_NODE:                newNode = std::make_shared<BswapNode>(*reinterpret_cast<BswapNode*>(node));       break;
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
        case FORALL_NODE:               newNode = std::make_shared<ForallNode>(*reinterpret_cast<ForallNode*>(node));     break;
        case IFF_NODE:                  newNode = std::make_shared<IffNode>(*reinterpret_cast<IffNode*>(node));           break;
        case INTEGER_NODE:              newNode = std::make_shared<IntegerNode>(*reinterpret_cast<IntegerNode*>(node));   break;
        case ITE_NODE:                  newNode = std::make_shared<IteNode>(*reinterpret_cast<IteNode*>(node));           break;
        case LAND_NODE:                 newNode = std::make_shared<LandNode>(*reinterpret_cast<LandNode*>(node));         break;
        case LET_NODE:                  newNode = std::make_shared<LetNode>(*reinterpret_cast<LetNode*>(node));           break;
        case LNOT_NODE:                 newNode = std::make_shared<LnotNode>(*reinterpret_cast<LnotNode*>(node));         break;
        case LOR_NODE:                  newNode = std::make_shared<LorNode>(*reinterpret_cast<LorNode*>(node));           break;
        case LXOR_NODE:                 newNode = std::make_shared<LxorNode>(*reinterpret_cast<LxorNode*>(node));         break;
        case REFERENCE_NODE: {
          if (unroll)
            return triton::ast::shallowCopy(reinterpret_cast<ReferenceNode*>(node)->getSymbolicExpression()->getAst().get(), unroll);
          else
            newNode = std::make_shared<ReferenceNode>(*reinterpret_cast<ReferenceNode*>(node));
          break;
        }
        case SELECT_NODE:               newNode = std::make_shared<SelectNode>(*reinterpret_cast<SelectNode*>(node));     break;
        case STORE_NODE:                newNode = std::make_shared<StoreNode>(*reinterpret_cast<StoreNode*>(node));       break;
        case STRING_NODE:               newNode = std::make_shared<StringNode>(*reinterpret_cast<StringNode*>(node));     break;
        case SX_NODE:                   newNode = std::make_shared<SxNode>(*reinterpret_cast<SxNode*>(node));             break;
        case VARIABLE_NODE:             newNode = node->shared_from_this(); /* Do not duplicate shared var (see #792) */  break;
        case ZX_NODE:                   newNode = std::make_shared<ZxNode>(*reinterpret_cast<ZxNode*>(node));             break;
        default:
          throw triton::exceptions::Ast("triton::ast::shallowCopy(): Invalid type node.");
      }

      if (newNode == nullptr)
        throw triton::exceptions::Ast("triton::ast::shallowCopy(): Not enough memory.");

      /* Remove parents as this is a new node which has no connections with original AST */
      if (node->getType() != VARIABLE_NODE) {
        /* VARIABLE_NODE are not duplicated (see #792), so don't remove their parents */
        auto parents = newNode->getParents();
        for (auto& p : parents) {
          newNode->removeParent(p.get());
        }
      }

      return node->getContext()->collect(newNode);
    }


    SharedAbstractNode newInstance(AbstractNode* node, bool unroll) {
      std::unordered_map<AbstractNode*, SharedAbstractNode> exprs;
      auto nodes = childrenExtraction(node->shared_from_this(), unroll, true);

      for (auto&& n : nodes) {
        /* Do a copy of all children */
        const auto& newNode = shallowCopy(n.get(), unroll);
        exprs[n.get()] = newNode;

        /* For each child, set its parent */
        auto& children = newNode->getChildren();
        for (auto& child : children) {
          child = exprs[child.get()];
          child->setParent(newNode.get());
        }
      }

      /* Return the root node */
      return exprs.at(node);
    }


    SharedAbstractNode unroll(const triton::ast::SharedAbstractNode& node) {
      return triton::ast::newInstance(node.get(), true);
    }


    /* Returns a vector of unique AST-nodes sorted topologically
     *
     * Depending on @descent argument this function produces topologically sorted vector of nodes from DAG consisting of
     * either parents or children of given @node. This helps to prevent exponential complexity when complex AST are
     * parsed during z3 conversion, copying and parents reinitialization.
     *
     * @unroll - traverses through ReferenceNodes
     * @revert - reverses the result
     * @descent - if true we traverse through children of nodes, otherwise parents
     */
    static std::vector<SharedAbstractNode> nodesExtraction(const SharedAbstractNode& node, bool unroll, bool revert, bool descend) {
      std::vector<SharedAbstractNode> result;
      std::unordered_set<AbstractNode*> visited;
      std::stack<std::pair<SharedAbstractNode, bool>> worklist;

      if (node == nullptr)
        throw triton::exceptions::Ast("triton::ast::nodesExtraction(): Node cannot be null.");

      /*
       *  We use a worklist strategy to avoid recursive calls
       *  and so stack overflow when going through a big AST.
       */
      worklist.push({node, false});

      while (!worklist.empty()) {
        SharedAbstractNode ast;
        bool postOrder;
        std::tie(ast, postOrder) = worklist.top();
        worklist.pop();

        /* It means that we visited all children of this node and we can put it in the result */
        if (postOrder) {
          result.push_back(ast);
          continue;
        }

        if (!visited.insert(ast.get()).second) {
          continue;
        }

        worklist.push({ast, true});

        const auto& relatives = descend ? ast->getChildren() : ast->getParents();

        /* Proceed relatives */
        for (const auto& r : relatives) {
          if (visited.find(r.get()) == visited.end()) {
            worklist.push({r, false});
          }
        }

        /* If unroll is true, we unroll all references */
        if (unroll && ast->getType() == REFERENCE_NODE) {
          const SharedAbstractNode& ref = reinterpret_cast<ReferenceNode*>(ast.get())->getSymbolicExpression()->getAst();
          if (visited.find(ref.get()) == visited.end()) {
            worklist.push({ref, false});
          }
        }
      }

      /* The result is in reversed topological sort meaning that children go before parents */
      if (!revert) {
        std::reverse(result.begin(), result.end());
      }

      return result;
    }


    std::vector<SharedAbstractNode> childrenExtraction(const SharedAbstractNode& node, bool unroll, bool revert) {
      return nodesExtraction(node, unroll, revert, true);
    }


    std::vector<SharedAbstractNode> parentsExtraction(const SharedAbstractNode& node, bool revert) {
      return nodesExtraction(node, false, revert, false);
    }


    std::deque<SharedAbstractNode> search(const SharedAbstractNode& node, triton::ast::ast_e match) {
      std::stack<AbstractNode*>                worklist;
      std::deque<SharedAbstractNode>           result;
      std::unordered_set<const AbstractNode*>  visited;

      worklist.push(node.get());
      while (!worklist.empty()) {
        AbstractNode* current = worklist.top();
        worklist.pop();

        // This means that node is already visited and we will not need to visited it second time
        if (visited.find(current) != visited.end()) {
          continue;
        }

        visited.insert(current);
        if (match == triton::ast::ANY_NODE || current->getType() == match)
          result.push_front(current->shared_from_this());

        if (current->getType() == REFERENCE_NODE) {
          worklist.push(reinterpret_cast<triton::ast::ReferenceNode*>(current)->getSymbolicExpression()->getAst().get());
        }
        else {
          for (const SharedAbstractNode& child : current->getChildren()) {
            worklist.push(child.get());
          }
        }
      }

      return result;
    }


    SharedAbstractNode dereference(const SharedAbstractNode& node) {
      AbstractNode* ptr = node.get();

      while (ptr->getType() == REFERENCE_NODE) {
        const ReferenceNode* ref = reinterpret_cast<const ReferenceNode*>(ptr);
        ptr = ref->getSymbolicExpression()->getAst().get();
      }

      return ptr->shared_from_this();
    }


    triton::uint32 getIndexSize(const SharedAbstractNode& node) {
      auto nref = triton::ast::dereference(node);
      switch(nref->getType()) {
        case ARRAY_NODE: return reinterpret_cast<ArrayNode*>(nref.get())->getIndexSize();
        case STORE_NODE: return reinterpret_cast<StoreNode*>(nref.get())->getIndexSize();
        default:
          throw triton::exceptions::Ast("triton::ast::getIndexSize(): The given node is not an array.");
      }
    }

  }; /* ast namespace */
}; /* triton namespace */
