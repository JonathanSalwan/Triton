//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AST_H
#define TRITON_AST_H

#include <tritonast/astEnums.hpp>

#include <tritoncore/types.hpp>

#include <list>
#include <map>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#include <memory>


//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    class Context;
    class AbstractNode;

    using SharedAbstractNode = std::shared_ptr<AbstractNode>;

    //! Abstract node
    class AbstractNode: public std::enable_shared_from_this<AbstractNode> {
      protected:
        //! The kind of the node.
        enum kind_e kind;

        //! The children of the node.
        std::vector<SharedAbstractNode> children;

        //! The parents of the node. Empty if there is still no parent.
        std::map<AbstractNode*, std::weak_ptr<AbstractNode>> parents;

        //! The size of the node.
        triton::uint32 size;

        //! The value of the tree from this root node.
        triton::uint512 eval;

        //! True if the tree contains a symbolic variable.
        bool symbolized;

        //! True if it's a logical node.
        bool logical;

        //! Contect use to create this node
        Context& ctxt;

      public:
        //! Constructor.
        AbstractNode(enum kind_e kind, Context& ctxt);

        //! Constructor by copy.
        AbstractNode(const AbstractNode& copy, Context& ctxt);

        //! Destructor.
        virtual ~AbstractNode();

        //! Access to its context
        Context& getContext(void) const;

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
        virtual triton::uint512 evaluate(void) const;

        //! Returns the children of the node.
        std::vector<SharedAbstractNode>& getChildren(void);

        /*!
         * \brief Returns the parents of node or an empty set if there is still no parent defined.
         */
        std::vector<SharedAbstractNode> getParents(void);

        void updateParents();

        //! Removes a parent node.
        void removeParent(AbstractNode* p);

        //! Sets a parent node.
        void setParent(AbstractNode* p);

        //! Sets the parent nodes.
        void setParent(std::vector<AbstractNode*>& p);

        //! Sets the size of the node.
        void setBitvectorSize(triton::uint32 size);

        //! Adds a child.
        void addChild(SharedAbstractNode const& child);

        //! Sets a child at an index.
        void setChild(triton::uint32 index, SharedAbstractNode const& child);

        //! Init stuffs like size and eval.
        virtual void init(void) = 0;

        //! Returns the has of the tree. The hash is computed recursively on the whole tree.
        virtual triton::uint512 hash(triton::uint32 deep) const = 0;
    };


    //! `(bvadd <expr1> <expr2>)` node
    class BvaddNode : public AbstractNode {
      public:
        // FIXME: Set override here
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvaddNode(Context& ctxt);
    };


    //! `(bvand <expr1> <expr2>)` node
    class BvandNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static std::shared_ptr<BvandNode> create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvandNode(Context& ctxt);
    };


    //! `(bvashr <expr1> <expr2>)` node
    class BvashrNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvashrNode(Context& ctxt);
    };


    //! `(bvlshr <expr1> <expr2>)` node
    class BvlshrNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvlshrNode(Context& ctxt);
    };


    //! `(bvmul <expr1> <expr2>)` node
    class BvmulNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvmulNode(Context& ctxt);
    };


    //! `(bvnand <expr1> <expr2>)` node
    class BvnandNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvnandNode(Context& ctxt);
    };


    //! `(bvneg <expr>)` node
    class BvnegNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr);

      private:
        BvnegNode(Context& ctxt);
    };


    //! `(bvnor <expr1> <expr2>)` node
    class BvnorNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvnorNode(Context& ctxt);
    };


    //! `(bvnot <expr>)` node
    class BvnotNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1);

      private:
        BvnotNode(Context& ctxt);
    };


    //! `(bvor <expr1> <expr2>)` node
    class BvorNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvorNode(Context& ctxt);
    };


    //! `((_ rotate_left rot) <expr>)` node
    class BvrolNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(triton::uint32 rot, SharedAbstractNode const& expr);
        static SharedAbstractNode create(SharedAbstractNode const& rot, SharedAbstractNode const& expr);

      private:
        BvrolNode(Context& ctxt);
    };


    //! `((_ rotate_right rot) <expr>)` node
    class BvrorNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(triton::uint32 rot, SharedAbstractNode const& expr);
        static SharedAbstractNode create(SharedAbstractNode const& rot, SharedAbstractNode const& expr);

      private:
        BvrorNode(Context& ctxt);
    };


    //! `(bvsdiv <expr1> <expr2>)` node
    class BvsdivNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsdivNode(Context& ctxt);
    };


    //! `(bvsge <expr1> <expr2>)` node
    class BvsgeNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsgeNode(Context& ctxt);
    };


    //! `(bvsgt <expr1> <expr2>)` node
    class BvsgtNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsgtNode(Context& ctxt);
    };


    //! `(bvshl <expr1> <expr2>)` node
    class BvshlNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvshlNode(Context& ctxt);
    };


    //! `(bvsle <expr1> <expr2>)` node
    class BvsleNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsleNode(Context& ctxt);
    };


    //! `(bvslt <expr1> <expr2>)` node
    class BvsltNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsltNode(Context& ctxt);
    };


    //! `(bvsmod <expr1> <expr2>)` node
    class BvsmodNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsmodNode(Context& ctxt);
    };


    //! `(bvsrem <expr1> <expr2>)` node
    class BvsremNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsremNode(Context& ctxt);
    };


    //! `(bvsub <expr1> <expr2>)` node
    class BvsubNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvsubNode(Context& ctxt);
    };


    //! `(bvudiv <expr1> <expr2>)` node
    class BvudivNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvudivNode(Context& ctxt);
    };


    //! `(bvuge <expr1> <expr2>)` node
    class BvugeNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvugeNode(Context& ctxt);
    };


    //! `(bvugt <expr1> <expr2>)` node
    class BvugtNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvugtNode(Context& ctxt);
    };


    //! `(bvule <expr1> <expr2>)` node
    class BvuleNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvuleNode(Context& ctxt);
    };


    //! `(bvult <expr1> <expr2>)` node
    class BvultNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvultNode(Context& ctxt);
    };


    //! `(bvurem <expr1> <expr2>)` node
    class BvuremNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvuremNode(Context& ctxt);
    };


    //! `(bvxnor <expr1> <expr2>)` node
    class BvxnorNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvxnorNode(Context& ctxt);
    };


    //! `(bvxor <expr1> <expr2>)` node
    class BvxorNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        BvxorNode(Context& ctxt);
    };


    //! `(_ bv<value> <size>)` node
    class BvNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(triton::uint512 value, triton::uint32 size, Context& ctxt);

      private:
        BvNode(Context& ctxt);
    };


    //! `(concat <expr1> <expr2> ...)` node
    class ConcatNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;

        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);
        template <typename T> static SharedAbstractNode create(const T& exprs, Context& ctxt);

      private:
        ConcatNode(Context& ctxt);
    };


    //! Decimal node
    class DecimalNode : public AbstractNode {
      protected:
        triton::uint512 value;

      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        triton::uint512 getValue(void);

        static SharedAbstractNode create(triton::uint512 value, Context& ctxt);

      private:
        DecimalNode(Context& ctxt);
    };


    //! `(distinct <expr1> <expr2> ...)` node
    class DistinctNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        DistinctNode(Context& ctxt);
    };


    //! `(= <expr1> <expr2> ...)` node
    class EqualNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);

      private:
        EqualNode(Context& ctxt);
    };


    //! `((_ extract <high> <low>) <expr>)` node
    class ExtractNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(triton::uint32 high, triton::uint32 low, SharedAbstractNode const& expr);

      private:
        ExtractNode(Context& ctxt);
    };


    //! `(ite <ifExpr> <thenExpr> <elseExpr>)`
    class IteNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& ifExpr, SharedAbstractNode const& thenExpr, SharedAbstractNode const& elseExpr);

      private:
        IteNode(Context& ctxt);
    };


    //! `(and <expr1> <expr2>)`
    class LandNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;

        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);
        template <class T> static SharedAbstractNode create(const T& exprs, Context& ctxt);

      private:
        LandNode(Context& ctxt);
    };


    //! `(let ((<alias> <expr2>)) <expr3>)`
    class LetNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(std::string alias, SharedAbstractNode const& expr2, SharedAbstractNode const& expr3);

      private:
        LetNode(Context& ctxt);
    };


    //! `(lnot <expr>)`
    class LnotNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr);

      private:
        LnotNode(Context& ctxt);
    };


    //! `(or <expr1> <expr2>)`
    class LorNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& expr1, SharedAbstractNode const& expr2);
        template <class T> static SharedAbstractNode create(const T& exprs, Context& ctxt);

      private:
        LorNode(Context& ctxt);
    };


    //! Reference node
    class ReferenceNode : public AbstractNode {
      protected:
        size_t id;
        SharedAbstractNode ast;

      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(SharedAbstractNode const& ast, size_t id, std::function<void()> const& end=nullptr);

        ~ReferenceNode();

        size_t getId() const;
        SharedAbstractNode const& getAst();

      private:
        std::function<void()> end_;
        ReferenceNode(SharedAbstractNode const& ast, size_t id, std::function<void()> const& end);
    };


    //! String node
    class StringNode : public AbstractNode {
      protected:
        std::string value;

      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(std::string value, Context& ctxt);
        std::string getValue(void);

      private:
        StringNode(std::string value, Context& ctxt);
    };


    //! `((_ sign_extend sizeExt) <expr>)` node
    class SxNode : public AbstractNode {
      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(triton::uint32 sizeExt, SharedAbstractNode const& expr);

      private:
        SxNode(Context& ctxt);
    };


    //! Variable node
    class VariableNode : public AbstractNode {
      protected:
        std::string varName;

      public:
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        std::string const& getVarName() const;
        static SharedAbstractNode create(std::string const& varName, triton::uint32 size, Context& ctxt);

      private:
        VariableNode(std::string const& varName, Context& ctxt);
    };


    //! `((_ zero_extend sizeExt) <expr>)` node
    class ZxNode : public AbstractNode {
      public:
        //! Create a zero extend of expr to sizeExt bits
        void init(void);
        triton::uint512 hash(triton::uint32 deep) const;
        static SharedAbstractNode create(triton::uint32 sizeExt, SharedAbstractNode const& expr);

      private:
        ZxNode(Context& ctxt);
    };


    //! Displays the node in ast representation.
    std::ostream& operator<<(std::ostream& stream, AbstractNode* node);

    //! AST C++ API - Duplicates the AST
    SharedAbstractNode newInstance(AbstractNode* node);

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
