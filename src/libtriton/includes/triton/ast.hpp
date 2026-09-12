//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_AST_H
#define TRITON_AST_H

#include <deque>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <triton/astEnums.hpp>
#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/dllexport.hpp>
#include <triton/exceptions.hpp>
#include <triton/tritonTypes.hpp>

//! The Triton namespace
namespace triton {
  /*!
   *  \addtogroup triton
   *  @{
   */

  /* Forward declarations */
  namespace engines {
    namespace symbolic {
      class SymbolicExpression;
      using SharedSymbolicExpression = std::shared_ptr<triton::engines::symbolic::SymbolicExpression>;

      class SymbolicVariable;
      using SharedSymbolicVariable = std::shared_ptr<triton::engines::symbolic::SymbolicVariable>;
    }; // namespace symbolic
  };   // namespace engines

  //! The AST namespace
  namespace ast {
    /*!
     *  \ingroup triton
     *  \addtogroup ast
     *  @{
     */

    class AstContext;
    class AbstractNode;

    //! Shared Abstract Node
    using SharedAbstractNode = std::shared_ptr<triton::ast::AbstractNode>;

    //! Weak Abstract Node
    using WeakAbstractNode = std::weak_ptr<triton::ast::AbstractNode>;

    //! Shared AST context
    using SharedAstContext = std::shared_ptr<triton::ast::AstContext>;

    //! Abstract node
    class AbstractNode : public std::enable_shared_from_this<AbstractNode> {
      private:
        //! Hashes the tree.
        virtual void initHash(void) = 0;

      protected:
        //! Deep level for computing hash
        triton::uint32 level;

        //! The type of the node.
        triton::ast::ast_e type;

        //! The children of the node.
        std::vector<SharedAbstractNode> children;

        // This structure counter the number of use of a given parent as a node may have
        // multiple time the same parent: eg. xor rax rax
        std::unordered_map<AbstractNode*, std::pair<triton::uint32, WeakAbstractNode>> parents;

        //! The size of the node.
        triton::uint32 size;

        //! The value of the tree from this root node.
        triton::uint512 eval;

        //! The hash of the tree
        triton::uint512 hash;

        //! True if the tree contains a symbolic variable.
        bool symbolized;

        //! True if it's a logical node.
        bool logical;

        //! True if it's an array node.
        bool array;

        //! Contect use to create this node
        SharedAstContext ctxt;

      public:
        //! Constructor.
        TRITON_EXPORT AbstractNode(triton::ast::ast_e type, const SharedAstContext& ctxt);

        //! Destructor.
        TRITON_EXPORT virtual ~AbstractNode();

        //! Access to its context
        TRITON_EXPORT SharedAstContext getContext(void) const;

        //! Returns the type of the node.
        TRITON_EXPORT triton::ast::ast_e getType(void) const;

        //! Returns the size of the node.
        TRITON_EXPORT triton::uint32 getBitvectorSize(void) const;

        //! Returns the vector mask according the size of the node.
        TRITON_EXPORT triton::uint512 getBitvectorMask(void) const;

        //! Returns true if it's an array node.
        TRITON_EXPORT bool isArray(void) const;

        //! According to the size of the expression, returns true if the MSB is 1.
        TRITON_EXPORT bool isSigned(void) const;

        //! Returns true if the tree contains a symbolic variable.
        TRITON_EXPORT bool isSymbolized(void) const;

        //! Returns true if it's a logical node.
        TRITON_EXPORT bool isLogical(void) const;

        //! Returns true if the node's concrete value and value type match those of the second one.
        TRITON_EXPORT bool hasSameConcreteValueAndTypeAs(const SharedAbstractNode& other) const;

        //! Returns true if the node's value, value type and properties match those of the second one.
        TRITON_EXPORT bool canReplaceNodeWithoutUpdate(const SharedAbstractNode& other) const;

        //! Returns true if the current tree is equal to the second one.
        TRITON_EXPORT bool equalTo(const SharedAbstractNode& other) const;

        //! Returns the deep level of the tree.
        TRITON_EXPORT triton::uint32 getLevel(void) const;

        //! Returns the hash of the tree.
        TRITON_EXPORT triton::uint512 getHash(void) const;

        //! Evaluates the tree.
        TRITON_EXPORT triton::uint512 evaluate(void) const;

        //! Initializes parents.
        void initParents(void);

        //! Returns the children of the node.
        TRITON_EXPORT std::vector<SharedAbstractNode>& getChildren(void);

        //! Returns the parents of node or an empty set if there is still no parent defined.
        TRITON_EXPORT std::vector<SharedAbstractNode> getParents(void);

        //! Removes a parent node.
        TRITON_EXPORT void removeParent(AbstractNode* p);

        //! Sets a parent node.
        TRITON_EXPORT void setParent(AbstractNode* p);

        //! Sets the parent nodes.
        TRITON_EXPORT void setParent(std::unordered_set<AbstractNode*>& p);

        //! Sets the size of the node.
        TRITON_EXPORT void setBitvectorSize(triton::uint32 size);

        //! Adds a child.
        TRITON_EXPORT void addChild(const SharedAbstractNode& child);

        //! Sets a child at an index.
        TRITON_EXPORT void setChild(triton::uint32 index, const SharedAbstractNode& child);

        //! Returns the string representation of the node.
        TRITON_EXPORT std::string str(void) const;

        //! Init properties of the node. If withParents is true, init also properties of parents
        TRITON_EXPORT virtual void init(bool withParents = false) = 0;
    };

    //! `(Array (_ BitVec indexSize) (_ BitVec 8))` node
    class ArrayNode : public AbstractNode {
      private:
        //! \brief Mapping of concrete values. It allows us to:
        //
        // (1) Synchronize the concrete and the symbolic
        // (2) Evaluate nodes
        std::unordered_map<triton::uint64, triton::uint8> memory;

        //! Size of array index
        triton::uint32 indexSize;

        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT ArrayNode(triton::uint32 indexSize, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(bool withParents = false);

        //! Stores a concrete value into the memory array
        TRITON_EXPORT void store(triton::uint64 addr, triton::uint8 value);

        //! Select a concrete value into the memory array
        TRITON_EXPORT triton::uint8 select(triton::uint64 addr) const;

        //! Select a concrete value into the memory array
        TRITON_EXPORT triton::uint8 select(const triton::uint512& addr) const;

        //! Select a concrete value into the memory array
        TRITON_EXPORT triton::uint8 select(const SharedAbstractNode& node) const;

        //! Gets the concrete memory array
        TRITON_EXPORT std::unordered_map<triton::uint64, triton::uint8>& getMemory(void);

        //! Gets the index size
        TRITON_EXPORT triton::uint32 getIndexSize(void) const;
    };

    //! `(assert <expr>)` node
    class AssertNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT AssertNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bswap <expr>)` node
    class BswapNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BswapNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvadd <expr1> <expr2>)` node
    class BvaddNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvaddNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvand <expr1> <expr2>)` node
    class BvandNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvashr <expr1> <expr2>)` node
    class BvashrNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvashrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvlshr <expr1> <expr2>)` node
    class BvlshrNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvlshrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvmul <expr1> <expr2>)` node
    class BvmulNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvmulNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvnand <expr1> <expr2>)` node
    class BvnandNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvnandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvneg <expr>)` node
    class BvnegNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvnegNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvnor <expr1> <expr2>)` node
    class BvnorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvnot <expr>)` node
    class BvnotNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvnotNode(const SharedAbstractNode& expr1);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvor <expr1> <expr2>)` node
    class BvorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `((_ rotate_left rot) <expr>)` node
    class BvrolNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvrolNode(const SharedAbstractNode& expr, triton::uint32 rot);
        TRITON_EXPORT BvrolNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `((_ rotate_right rot) <expr>)` node
    class BvrorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvrorNode(const SharedAbstractNode& expr, triton::uint32 rot);
        TRITON_EXPORT BvrorNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsdiv <expr1> <expr2>)` node
    class BvsdivNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsdivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsge <expr1> <expr2>)` node
    class BvsgeNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsgeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsgt <expr1> <expr2>)` node
    class BvsgtNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsgtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvshl <expr1> <expr2>)` node
    class BvshlNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvshlNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsle <expr1> <expr2>)` node
    class BvsleNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvslt <expr1> <expr2>)` node
    class BvsltNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsltNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsmod <expr1> <expr2>)` node
    class BvsmodNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsmodNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsrem <expr1> <expr2>)` node
    class BvsremNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvsub <expr1> <expr2>)` node
    class BvsubNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvsubNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvudiv <expr1> <expr2>)` node
    class BvudivNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvudivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvuge <expr1> <expr2>)` node
    class BvugeNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvugeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvugt <expr1> <expr2>)` node
    class BvugtNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvugtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvule <expr1> <expr2>)` node
    class BvuleNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvuleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvult <expr1> <expr2>)` node
    class BvultNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvultNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvurem <expr1> <expr2>)` node
    class BvuremNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvuremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvxnor <expr1> <expr2>)` node
    class BvxnorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvxnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(bvxor <expr1> <expr2>)` node
    class BvxorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(_ bv<value> <size>)` node
    class BvNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT BvNode(const triton::uint512& value, triton::uint32 size, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `[<expr1> <expr2> <expr3> ...]` node
    class CompoundNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        template <typename T>
        CompoundNode(const T& exprs, const SharedAstContext& ctxt)
            : AbstractNode(COMPOUND_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(concat <expr1> <expr2> ...)` node
    class ConcatNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        template <typename T>
        ConcatNode(const T& exprs, const SharedAstContext& ctxt)
            : AbstractNode(CONCAT_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT ConcatNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(declare-fun <var_name> () (_ BitVec <var_size>))` node
    class DeclareNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT DeclareNode(const SharedAbstractNode& var);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(distinct <expr1> <expr2> ...)` node
    class DistinctNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT DistinctNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(= <expr1> <expr2> ...)` node
    class EqualNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT EqualNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `((_ extract <high> <low>) <expr>)` node
    class ExtractNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT ExtractNode(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(forall ((x (_ BitVec <size>)), ...) body)`
    class ForallNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        template <typename T>
        ForallNode(const T& vars, const SharedAbstractNode& body)
            : AbstractNode(FORALL_NODE, body->getContext()) {
          for (auto var : vars)
            this->addChild(var);
          this->addChild(body);
        }

        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(iff <expr1> <expr2>)`
    class IffNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT IffNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! Integer node
    class IntegerNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      protected:
        triton::uint512 value;

      public:
        TRITON_EXPORT IntegerNode(const triton::uint512& value, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(bool withParents = false);
        TRITON_EXPORT triton::uint512 getInteger(void);
    };

    //! `(ite <ifExpr> <thenExpr> <elseExpr>)`
    class IteNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT IteNode(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr,
                              const SharedAbstractNode& elseExpr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(and <expr1> <expr2>)`
    class LandNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        template <typename T>
        LandNode(const T& exprs, const SharedAstContext& ctxt)
            : AbstractNode(LAND_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT LandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(let ((<alias> <expr2>)) <expr3>)`
    class LetNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT LetNode(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(lnot <expr>)`
    class LnotNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT LnotNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(or <expr1> <expr2>)`
    class LorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        template <typename T>
        LorNode(const T& exprs, const SharedAstContext& ctxt)
            : AbstractNode(LOR_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT LorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(xor <expr1> <expr2>)`
    class LxorNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        template <typename T>
        LxorNode(const T& exprs, const SharedAstContext& ctxt)
            : AbstractNode(LXOR_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT LxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! Reference node
    class ReferenceNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      protected:
        triton::engines::symbolic::SharedSymbolicExpression expr;

      public:
        TRITON_EXPORT ReferenceNode(const triton::engines::symbolic::SharedSymbolicExpression& expr);
        TRITON_EXPORT void init(bool withParents = false);
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& getSymbolicExpression(void) const;
    };

    //! `(select array index)`
    class SelectNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT SelectNode(const SharedAbstractNode& array, triton::usize index);
        TRITON_EXPORT SelectNode(const SharedAbstractNode& array, const SharedAbstractNode& index);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! `(store array index expr)`
    class StoreNode : public AbstractNode {
      private:
        //! \brief Mapping of concrete values. It allows us to:
        //
        // (1) Synchronize the concrete and the symbolic
        // (2) Evaluate nodes
        std::unordered_map<triton::uint64, triton::uint8> memory;

        //! Size of array index
        triton::uint32 indexSize;

        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT StoreNode(const SharedAbstractNode& array, triton::usize index, const SharedAbstractNode& expr);
        TRITON_EXPORT StoreNode(const SharedAbstractNode& array, const SharedAbstractNode& index,
                                const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);

        //! Select a concrete value into the memory array
        TRITON_EXPORT triton::uint8 select(triton::uint64 addr) const;

        //! Select a concrete value into the memory array
        TRITON_EXPORT triton::uint8 select(const triton::uint512& addr) const;

        //! Select a concrete value into the memory array
        TRITON_EXPORT triton::uint8 select(const SharedAbstractNode& node) const;

        //! Gets the concrete memory array
        TRITON_EXPORT std::unordered_map<triton::uint64, triton::uint8>& getMemory(void);

        //! Gets the index size
        TRITON_EXPORT triton::uint32 getIndexSize(void) const;
    };

    //! String node
    class StringNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      protected:
        std::string value;

      public:
        TRITON_EXPORT StringNode(std::string value, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(bool withParents = false);
        TRITON_EXPORT std::string getString(void);
    };

    //! `((_ sign_extend sizeExt) <expr>)` node
    class SxNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        TRITON_EXPORT SxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! Variable node
    class VariableNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      protected:
        triton::engines::symbolic::SharedSymbolicVariable symVar;

      public:
        TRITON_EXPORT VariableNode(const triton::engines::symbolic::SharedSymbolicVariable& symVar,
                                   const SharedAstContext& ctxt);
        TRITON_EXPORT void init(bool withParents = false);
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicVariable& getSymbolicVariable(void);
    };

    //! `((_ zero_extend sizeExt) <expr>)` node
    class ZxNode : public AbstractNode {
      private:
        TRITON_EXPORT void initHash(void);

      public:
        //! Create a zero extend of expr to sizeExt bits
        TRITON_EXPORT ZxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr);
        TRITON_EXPORT void init(bool withParents = false);
    };

    //! Custom hash2n function for hash routine.
    triton::uint512 hash2n(triton::uint512 hash, triton::uint32 n);

    //! Custom rotate left function for hash routine.
    triton::uint512 rotl(const triton::uint512& value, triton::uint32 shift);

    //! Custom modular sign extend for bitwise operation.
    triton::sint512 modularSignExtend(AbstractNode* node);

    //! Displays the node in ast representation.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, AbstractNode* node);

    //! AST C++ API - Duplicates the AST
    TRITON_EXPORT SharedAbstractNode newInstance(AbstractNode* node, bool unroll = false);

    //! AST C++ API - Unrolls the SSA form of a given AST.
    TRITON_EXPORT SharedAbstractNode unroll(const SharedAbstractNode& node);

    //! Returns node and all its children of an AST sorted topologically. If `unroll` is true, references are unrolled.
    //! If `revert` is true, children are on top of list.
    TRITON_EXPORT std::vector<SharedAbstractNode> childrenExtraction(const SharedAbstractNode& node, bool unroll,
                                                                     bool revert);

    //! Returns node and all its parents of an AST sorted topologically. If `revert` is true, oldest parents are on top
    //! of list.
    TRITON_EXPORT std::vector<SharedAbstractNode> parentsExtraction(const SharedAbstractNode& node, bool revert);

    //! Returns a deque of collected matched nodes via a depth-first pre order traversal.
    TRITON_EXPORT std::deque<SharedAbstractNode> search(const SharedAbstractNode& node,
                                                        triton::ast::ast_e match = ANY_NODE);

    //! Returns the first non referene node encountered.
    TRITON_EXPORT SharedAbstractNode dereference(const SharedAbstractNode& node);

    //! Gets the index size of an array
    triton::uint32 getIndexSize(const SharedAbstractNode& node);

    //! Gets the value of an integer node.
    template <typename T> T inline getInteger(const SharedAbstractNode& node) {
      if (node->getType() == INTEGER_NODE) {
        return static_cast<T>(reinterpret_cast<IntegerNode*>(node.get())->getInteger());
      }
      throw triton::exceptions::Ast("triton::ast::getInteger(): You must provide an INTEGER_NODE.");
    }

    //! std::string specialization
    template <> std::string inline getInteger(const SharedAbstractNode& node) {
      if (node->getType() == INTEGER_NODE) {
        return triton::utils::toString(reinterpret_cast<triton::ast::IntegerNode*>(node.get())->getInteger());
      }
      throw triton::exceptions::Ast("triton::ast::getInteger(): You must provide an INTEGER_NODE.");
    }

    /*! @} End of ast namespace */
  }; // namespace ast
  /*! @} End of triton namespace */
}; // namespace triton

#endif /* TRITON_AST_H */
