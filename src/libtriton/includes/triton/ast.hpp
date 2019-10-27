//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AST_H
#define TRITON_AST_H

#include <deque>
#include <map>
#include <memory>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include <triton/astEnums.hpp>
#include <triton/cpuSize.hpp>
#include <triton/triton_export.h>
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
    };
  };

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
      protected:
        //! The type of the node.
        triton::ast::ast_e type;

        //! The children of the node.
        std::vector<SharedAbstractNode> children;

        // This structure counter the number of use of a given parent as a node may have
        // multiple time the same parent: eg. xor rax rax
        std::map<AbstractNode*, std::pair<triton::uint32, WeakAbstractNode>> parents;

        //! The size of the node.
        triton::uint32 size;

        //! The value of the tree from this root node.
        triton::uint512 eval;

        //! True if the tree contains a symbolic variable.
        bool symbolized;

        //! True if it's a logical node.
        bool logical;

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

        //! According to the size of the expression, returns true if the MSB is 1.
        TRITON_EXPORT bool isSigned(void) const;

        //! Returns true if the tree contains a symbolic variable.
        TRITON_EXPORT bool isSymbolized(void) const;

        //! Returns true if it's a logical node.
        TRITON_EXPORT bool isLogical(void) const;

        //! Returns true if the current tree is equal to the second one.
        TRITON_EXPORT bool equalTo(const SharedAbstractNode&) const;

        //! Evaluates the tree.
        TRITON_EXPORT virtual triton::uint512 evaluate(void) const;

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
        TRITON_EXPORT void setParent(std::set<AbstractNode*>& p);

        //! Sets the size of the node.
        TRITON_EXPORT void setBitvectorSize(triton::uint32 size);

        //! Adds a child.
        TRITON_EXPORT void addChild(const SharedAbstractNode& child);

        //! Sets a child at an index.
        TRITON_EXPORT void setChild(triton::uint32 index, const SharedAbstractNode& child);

        //! Returns the string representation of the node.
        TRITON_EXPORT std::string str(void) const;

        //! Init stuffs like size and eval.
        TRITON_EXPORT virtual void init(void) = 0;

        //! Returns the has of the tree. The hash is computed recursively on the whole tree.
        TRITON_EXPORT virtual triton::uint512 hash(triton::uint32 deep) const = 0;
    };


    //! `(assert <expr>)` node
    class AssertNode : public AbstractNode {
      public:
        TRITON_EXPORT AssertNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvadd <expr1> <expr2>)` node
    class BvaddNode : public AbstractNode {
      public:
        TRITON_EXPORT BvaddNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvand <expr1> <expr2>)` node
    class BvandNode : public AbstractNode {
      public:
        TRITON_EXPORT BvandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvashr <expr1> <expr2>)` node
    class BvashrNode : public AbstractNode {
      public:
        TRITON_EXPORT BvashrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvlshr <expr1> <expr2>)` node
    class BvlshrNode : public AbstractNode {
      public:
        TRITON_EXPORT BvlshrNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvmul <expr1> <expr2>)` node
    class BvmulNode : public AbstractNode {
      public:
        TRITON_EXPORT BvmulNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnand <expr1> <expr2>)` node
    class BvnandNode : public AbstractNode {
      public:
        TRITON_EXPORT BvnandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvneg <expr>)` node
    class BvnegNode : public AbstractNode {
      public:
        TRITON_EXPORT BvnegNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnor <expr1> <expr2>)` node
    class BvnorNode : public AbstractNode {
      public:
        TRITON_EXPORT BvnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnot <expr>)` node
    class BvnotNode : public AbstractNode {
      public:
        TRITON_EXPORT BvnotNode(const SharedAbstractNode& expr1);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvor <expr1> <expr2>)` node
    class BvorNode : public AbstractNode {
      public:
        TRITON_EXPORT BvorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ rotate_left rot) <expr>)` node
    class BvrolNode : public AbstractNode {
      public:
        TRITON_EXPORT BvrolNode(const SharedAbstractNode& expr, triton::uint32 rot);
        TRITON_EXPORT BvrolNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ rotate_right rot) <expr>)` node
    class BvrorNode : public AbstractNode {
      public:
        TRITON_EXPORT BvrorNode(const SharedAbstractNode& expr, triton::uint32 rot);
        TRITON_EXPORT BvrorNode(const SharedAbstractNode& expr, const SharedAbstractNode& rot);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsdiv <expr1> <expr2>)` node
    class BvsdivNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsdivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsge <expr1> <expr2>)` node
    class BvsgeNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsgeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsgt <expr1> <expr2>)` node
    class BvsgtNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsgtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvshl <expr1> <expr2>)` node
    class BvshlNode : public AbstractNode {
      public:
        TRITON_EXPORT BvshlNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsle <expr1> <expr2>)` node
    class BvsleNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvslt <expr1> <expr2>)` node
    class BvsltNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsltNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsmod <expr1> <expr2>)` node
    class BvsmodNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsmodNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsrem <expr1> <expr2>)` node
    class BvsremNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsub <expr1> <expr2>)` node
    class BvsubNode : public AbstractNode {
      public:
        TRITON_EXPORT BvsubNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvudiv <expr1> <expr2>)` node
    class BvudivNode : public AbstractNode {
      public:
        TRITON_EXPORT BvudivNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvuge <expr1> <expr2>)` node
    class BvugeNode : public AbstractNode {
      public:
        TRITON_EXPORT BvugeNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvugt <expr1> <expr2>)` node
    class BvugtNode : public AbstractNode {
      public:
        TRITON_EXPORT BvugtNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvule <expr1> <expr2>)` node
    class BvuleNode : public AbstractNode {
      public:
        TRITON_EXPORT BvuleNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvult <expr1> <expr2>)` node
    class BvultNode : public AbstractNode {
      public:
        TRITON_EXPORT BvultNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvurem <expr1> <expr2>)` node
    class BvuremNode : public AbstractNode {
      public:
        TRITON_EXPORT BvuremNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvxnor <expr1> <expr2>)` node
    class BvxnorNode : public AbstractNode {
      public:
        TRITON_EXPORT BvxnorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvxor <expr1> <expr2>)` node
    class BvxorNode : public AbstractNode {
      public:
        TRITON_EXPORT BvxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(_ bv<value> <size>)` node
    class BvNode : public AbstractNode {
      public:
        TRITON_EXPORT BvNode(const triton::uint512& value, triton::uint32 size, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `[<expr1> <expr2> <expr3> ...]` node
    class CompoundNode : public AbstractNode {
      public:
        template <typename T> CompoundNode(const T& exprs, const SharedAstContext& ctxt)
          : AbstractNode(COMPOUND_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(concat <expr1> <expr2> ...)` node
    class ConcatNode : public AbstractNode {
      public:
        template <typename T> ConcatNode(const T& exprs, const SharedAstContext& ctxt)
          : AbstractNode(CONCAT_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT ConcatNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(declare-fun <var_name> () (_ BitVec <var_size>))` node
    class DeclareNode : public AbstractNode {
      public:
        TRITON_EXPORT DeclareNode(const SharedAbstractNode& var);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(distinct <expr1> <expr2> ...)` node
    class DistinctNode : public AbstractNode {
      public:
        TRITON_EXPORT DistinctNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(= <expr1> <expr2> ...)` node
    class EqualNode : public AbstractNode {
      public:
        TRITON_EXPORT EqualNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ extract <high> <low>) <expr>)` node
    class ExtractNode : public AbstractNode {
      public:
        TRITON_EXPORT ExtractNode(triton::uint32 high, triton::uint32 low, const SharedAbstractNode& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(iff <expr1> <expr2>)`
    class IffNode : public AbstractNode {
      public:
        TRITON_EXPORT IffNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Integer node
    class IntegerNode : public AbstractNode {
      protected:
        triton::uint512 value;

      public:
        TRITON_EXPORT IntegerNode(const triton::uint512& value, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
        TRITON_EXPORT triton::uint512 getInteger(void);
    };


    //! `(ite <ifExpr> <thenExpr> <elseExpr>)`
    class IteNode : public AbstractNode {
      public:
        TRITON_EXPORT IteNode(const SharedAbstractNode& ifExpr, const SharedAbstractNode& thenExpr, const SharedAbstractNode& elseExpr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(and <expr1> <expr2>)`
    class LandNode : public AbstractNode {
      public:
        template <typename T> LandNode(const T& exprs, const SharedAstContext& ctxt)
          : AbstractNode(LAND_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT LandNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(let ((<alias> <expr2>)) <expr3>)`
    class LetNode : public AbstractNode {
      public:
        TRITON_EXPORT LetNode(std::string alias, const SharedAbstractNode& expr2, const SharedAbstractNode& expr3);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(lnot <expr>)`
    class LnotNode : public AbstractNode {
      public:
        TRITON_EXPORT LnotNode(const SharedAbstractNode& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(or <expr1> <expr2>)`
    class LorNode : public AbstractNode {
      public:
        template <typename T> LorNode(const T& exprs, const SharedAstContext& ctxt)
          : AbstractNode(LOR_NODE, ctxt) {
          for (auto expr : exprs)
            this->addChild(expr);
        }

        TRITON_EXPORT LorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(xor <expr1> <expr2>)`
    class LxorNode : public AbstractNode {
    public:
      template <typename T> LxorNode(const T& exprs, const SharedAstContext& ctxt)
        : AbstractNode(LXOR_NODE, ctxt) {
        for (auto expr : exprs)
          this->addChild(expr);
      }

      TRITON_EXPORT LxorNode(const SharedAbstractNode& expr1, const SharedAbstractNode& expr2);
      TRITON_EXPORT void init(void);
      TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Reference node
    class ReferenceNode : public AbstractNode {
      protected:
        triton::engines::symbolic::SharedSymbolicExpression expr;

      public:
        TRITON_EXPORT ReferenceNode(const triton::engines::symbolic::SharedSymbolicExpression& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicExpression& getSymbolicExpression(void) const;
    };


    //! String node
    class StringNode : public AbstractNode {
      protected:
        std::string value;

      public:
        TRITON_EXPORT StringNode(std::string value, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
        TRITON_EXPORT std::string getString(void);
    };


    //! `((_ sign_extend sizeExt) <expr>)` node
    class SxNode : public AbstractNode {
      public:
        TRITON_EXPORT SxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Variable node
    class VariableNode : public AbstractNode {
      protected:
        triton::engines::symbolic::SharedSymbolicVariable symVar;

      public:
        TRITON_EXPORT VariableNode(const triton::engines::symbolic::SharedSymbolicVariable& symVar, const SharedAstContext& ctxt);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
        TRITON_EXPORT const triton::engines::symbolic::SharedSymbolicVariable& getSymbolicVariable(void);
    };


    //! `((_ zero_extend sizeExt) <expr>)` node
    class ZxNode : public AbstractNode {
      public:
        //! Create a zero extend of expr to sizeExt bits
        TRITON_EXPORT ZxNode(triton::uint32 sizeExt, const SharedAbstractNode& expr);
        TRITON_EXPORT void init(void);
        TRITON_EXPORT triton::uint512 hash(triton::uint32 deep) const;
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
    TRITON_EXPORT SharedAbstractNode newInstance(AbstractNode* node, bool unroll=false);

    //! AST C++ API - Unrolls the SSA form of a given AST.
    TRITON_EXPORT SharedAbstractNode unroll(const SharedAbstractNode& node);

    //! Returns all nodes of an AST. If `unroll` is true, references are unrolled. If `revert` is true, children are on top of list.
    TRITON_EXPORT void nodesExtraction(std::deque<SharedAbstractNode>* output, const SharedAbstractNode& node, bool unroll, bool revert);

    //! Returns a deque of collected matched nodes via a depth-first pre order traversal.
    TRITON_EXPORT std::deque<SharedAbstractNode> search(const SharedAbstractNode& node, triton::ast::ast_e match=ANY_NODE);

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AST_H */
