//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AST_H
#define TRITON_AST_H

#include <list>
#include <map>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include <triton/astEnums.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  namespace engines {
    namespace symbolic {
      class SymbolicExpression;
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

    //! Abstract node
    class AbstractNode {
      protected:
        //! The kind of the node.
        enum kind_e kind;

        //! The children of the node.
        std::vector<AbstractNode*> children;

        //! The parents of the node. Empty if there is still no parent.
        std::set<AbstractNode*> parents;

        //! The size of the node.
        triton::uint32 size;

        //! The value of the tree from this root node.
        triton::uint512 eval;

        //! True if the tree contains a symbolic variable.
        bool symbolized;

        //! True if it's a logical node.
        bool logical;

        //! Contect use to create this node
        AstContext& ctxt;

      public:
        //! Constructor.
        AbstractNode(enum kind_e kind, AstContext& ctxt);

        //! Constructor by copy.
        AbstractNode(const AbstractNode& copy, AstContext& ctxt);

        //! Destructor.
        virtual ~AbstractNode();

        //! Access to its context
        AstContext& getContext(void) const;

        //! Returns the kind of the node.
        enum kind_e getKind(void) const;

        //! Returns the size of the node.
        triton::uint32 getBitvectorSize(void) const;

        //! Returns the vector mask according the size of the node.
        triton::uint512 getBitvectorMask(void) const;

        //! According to the size of the expression, returns true if the MSB is 1.
        bool isSigned(void) const;

        //! Returns true if the tree contains a symbolic variable.
        bool isSymbolized(void) const;

        //! Returns true if it's a logical node.
        bool isLogical(void) const;

        //! Returns true if the current tree is equal to the second one.
        bool equalTo(const AbstractNode&) const;

        //! Returns true if the current tree is equal to the second one.
        bool equalTo(AbstractNode*) const;

        //! Evaluates the tree.
        triton::uint512 evaluate(void) const;

        //! Returns the children of the node.
        std::vector<AbstractNode*>& getChildren(void);

        /*!
         * \brief Returns the parents of node or an empty set if there is still no parent defined.
         *
         * Note that if there is the `AST_DICTIONARIES` optimization enabled, this feature will
         * probably not represent the real tree of your expression.
         */
        std::set<AbstractNode*>& getParents(void);

        //! Removes a parent node.
        void removeParent(AbstractNode* p);

        //! Sets a parent node.
        void setParent(AbstractNode* p);

        //! Sets the parent nodes.
        void setParent(std::set<AbstractNode*>& p);

        //! Sets the size of the node.
        void setBitvectorSize(triton::uint32 size);

        //! Adds a child.
        void addChild(AbstractNode* child);

        //! Sets a child at an index.
        void setChild(triton::uint32 index, AbstractNode* child);

        //! Init stuffs like size and eval.
        virtual void init(void) = 0;

        //! Returns the has of the tree. The hash is computed recursively on the whole tree.
        virtual triton::uint512 hash(triton::uint32 deep) const = 0;
    };


    //! `(bvadd <expr1> <expr2>)` node
    class BvaddNode : public AbstractNode {
      public:
        BvaddNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvand <expr1> <expr2>)` node
    class BvandNode : public AbstractNode {
      public:
        BvandNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvashr <expr1> <expr2>)` node
    class BvashrNode : public AbstractNode {
      public:
        BvashrNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvlshr <expr1> <expr2>)` node
    class BvlshrNode : public AbstractNode {
      public:
        BvlshrNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvmul <expr1> <expr2>)` node
    class BvmulNode : public AbstractNode {
      public:
        BvmulNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnand <expr1> <expr2>)` node
    class BvnandNode : public AbstractNode {
      public:
        BvnandNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvneg <expr>)` node
    class BvnegNode : public AbstractNode {
      public:
        BvnegNode(AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnor <expr1> <expr2>)` node
    class BvnorNode : public AbstractNode {
      public:
        BvnorNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnot <expr>)` node
    class BvnotNode : public AbstractNode {
      public:
        BvnotNode(AbstractNode* expr1);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvor <expr1> <expr2>)` node
    class BvorNode : public AbstractNode {
      public:
        BvorNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ rotate_left rot) <expr>)` node
    class BvrolNode : public AbstractNode {
      public:
        BvrolNode(triton::uint32 rot, AbstractNode* expr);
        BvrolNode(AbstractNode* rot, AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ rotate_right rot) <expr>)` node
    class BvrorNode : public AbstractNode {
      public:
        BvrorNode(triton::uint32 rot, AbstractNode* expr);
        BvrorNode(AbstractNode* rot, AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsdiv <expr1> <expr2>)` node
    class BvsdivNode : public AbstractNode {
      public:
        BvsdivNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsge <expr1> <expr2>)` node
    class BvsgeNode : public AbstractNode {
      public:
        BvsgeNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsgt <expr1> <expr2>)` node
    class BvsgtNode : public AbstractNode {
      public:
        BvsgtNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvshl <expr1> <expr2>)` node
    class BvshlNode : public AbstractNode {
      public:
        BvshlNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsle <expr1> <expr2>)` node
    class BvsleNode : public AbstractNode {
      public:
        BvsleNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvslt <expr1> <expr2>)` node
    class BvsltNode : public AbstractNode {
      public:
        BvsltNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsmod <expr1> <expr2>)` node
    class BvsmodNode : public AbstractNode {
      public:
        BvsmodNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsrem <expr1> <expr2>)` node
    class BvsremNode : public AbstractNode {
      public:
        BvsremNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsub <expr1> <expr2>)` node
    class BvsubNode : public AbstractNode {
      public:
        BvsubNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvudiv <expr1> <expr2>)` node
    class BvudivNode : public AbstractNode {
      public:
        BvudivNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvuge <expr1> <expr2>)` node
    class BvugeNode : public AbstractNode {
      public:
        BvugeNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvugt <expr1> <expr2>)` node
    class BvugtNode : public AbstractNode {
      public:
        BvugtNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvule <expr1> <expr2>)` node
    class BvuleNode : public AbstractNode {
      public:
        BvuleNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvult <expr1> <expr2>)` node
    class BvultNode : public AbstractNode {
      public:
        BvultNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvurem <expr1> <expr2>)` node
    class BvuremNode : public AbstractNode {
      public:
        BvuremNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvxnor <expr1> <expr2>)` node
    class BvxnorNode : public AbstractNode {
      public:
        BvxnorNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvxor <expr1> <expr2>)` node
    class BvxorNode : public AbstractNode {
      public:
        BvxorNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(_ bv<value> <size>)` node
    class BvNode : public AbstractNode {
      public:
        BvNode(triton::uint512 value, triton::uint32 size, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(concat <expr1> <expr2> ...)` node
    class ConcatNode : public AbstractNode {
      public:
        ConcatNode(AbstractNode* expr1, AbstractNode* expr2);
        template <typename T> ConcatNode(const T& exprs, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Decimal node
    class DecimalNode : public AbstractNode {
      protected:
        triton::uint512 value;

      public:
        DecimalNode(triton::uint512 value, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        triton::uint512 getValue(void);
    };


    //! `(distinct <expr1> <expr2> ...)` node
    class DistinctNode : public AbstractNode {
      public:
        DistinctNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(= <expr1> <expr2> ...)` node
    class EqualNode : public AbstractNode {
      public:
        EqualNode(AbstractNode* expr1, AbstractNode* expr2);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ extract <high> <low>) <expr>)` node
    class ExtractNode : public AbstractNode {
      public:
        ExtractNode(triton::uint32 high, triton::uint32 low, AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(ite <ifExpr> <thenExpr> <elseExpr>)`
    class IteNode : public AbstractNode {
      public:
        IteNode(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(and <expr1> <expr2>)`
    class LandNode : public AbstractNode {
      public:
        LandNode(AbstractNode* expr1, AbstractNode* expr2);
        template <typename T> LandNode(const T& exprs, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(let ((<alias> <expr2>)) <expr3>)`
    class LetNode : public AbstractNode {
      public:
        LetNode(std::string alias, AbstractNode* expr2, AbstractNode* expr3);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(lnot <expr>)`
    class LnotNode : public AbstractNode {
      public:
        LnotNode(AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(or <expr1> <expr2>)`
    class LorNode : public AbstractNode {
      public:
        LorNode(AbstractNode* expr1, AbstractNode* expr2);
        template <typename T> LorNode(const T& exprs, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Reference node
    class ReferenceNode : public AbstractNode {
      protected:
        triton::engines::symbolic::SymbolicExpression& expr;

      public:
        ReferenceNode(triton::engines::symbolic::SymbolicExpression& expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        triton::engines::symbolic::SymbolicExpression& getSymbolicExpression(void) const;
    };


    //! String node
    class StringNode : public AbstractNode {
      protected:
        std::string value;

      public:
        StringNode(std::string value, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        std::string getValue(void);
    };


    //! `((_ sign_extend sizeExt) <expr>)` node
    class SxNode : public AbstractNode {
      public:
        SxNode(triton::uint32 sizeExt, AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Variable node
    class VariableNode : public AbstractNode {
      protected:
        triton::engines::symbolic::SymbolicVariable& symVar;

      public:
        VariableNode(triton::engines::symbolic::SymbolicVariable& symVar, AstContext& ctxt);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        triton::engines::symbolic::SymbolicVariable& getVar(void);
    };


    //! `((_ zero_extend sizeExt) <expr>)` node
    class ZxNode : public AbstractNode {
      public:
        //! Create a zero extend of expr to sizeExt bits
        ZxNode(triton::uint32 sizeExt, AbstractNode* expr);
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Displays the node in ast representation.
    std::ostream& operator<<(std::ostream& stream, AbstractNode* node);

    //! AST C++ API - Duplicates the AST
    AbstractNode* newInstance(AbstractNode* node);

    //! Custom pow function for hash routine.
    triton::uint512 pow(triton::uint512 hash, triton::uint32 n);

    //! Custom rotate left function for hash routine.
    triton::uint512 rotl(triton::uint512 value, triton::uint32 shift);

    //! Custom modular sign extend for bitwise operation.
    triton::sint512 modularSignExtend(AbstractNode* node);

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_AST_H */
