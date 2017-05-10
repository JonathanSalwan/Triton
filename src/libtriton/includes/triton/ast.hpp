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
#include <triton/astVisitor.hpp>
#include <triton/symbolicVariable.hpp>
#include <triton/tritonTypes.hpp>



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

    //! Abstract node
    class AbstractNode {
      protected:
        //! The kind of the node.
        enum kind_e kind;

        //! The childs of the node.
        std::vector<AbstractNode*> childs;

        //! The parents of the node. Empty if there is still no parent.
        std::set<AbstractNode*> parents;

        //! The size of the node.
        triton::uint32 size;

        //! The value of the tree from this root node.
        triton::uint512 eval;

        //! This value is set to true if the tree contains a symbolic variable.
        bool symbolized;

      public:
        //! Constructor.
        AbstractNode(enum kind_e kind);

        //! Constructor by copy.
        AbstractNode(const AbstractNode& copy);

        //! Constructor.
        AbstractNode();

        //! Destructor.
        virtual ~AbstractNode();

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

        //! Returns true if the current tree is equal to the second one.
        bool equalTo(const AbstractNode&) const;

        //! Returns true if the current tree is equal to the second one.
        bool equalTo(AbstractNode*) const;

        //! Evaluates the tree.
        triton::uint512 evaluate(void) const;

        //! Returns the childs of the node.
        std::vector<AbstractNode*>& getChilds(void);

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

        //! Entry point for a visitor.
        virtual void accept(AstVisitor& v) = 0;

        //! Returns the has of the tree. The hash is computed recursively on the whole tree.
        virtual triton::uint512 hash(triton::uint32 deep) const = 0;
    };


    //! `(assert <expr1>)` node
    class AssertNode : public AbstractNode {
      public:
        AssertNode(AbstractNode* expr);
        AssertNode(const AssertNode& copy);
        virtual ~AssertNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvadd <expr1> <expr2>)` node
    class BvaddNode : public AbstractNode {
      public:
        BvaddNode(AbstractNode* expr1, AbstractNode* expr2);
        BvaddNode(const BvaddNode& copy);
        virtual ~BvaddNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvand <expr1> <expr2>)` node
    class BvandNode : public AbstractNode {
      public:
        BvandNode(AbstractNode* expr1, AbstractNode* expr2);
        BvandNode(const BvandNode& copy);
        virtual ~BvandNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvashr <expr1> <expr2>)` node
    class BvashrNode : public AbstractNode {
      public:
        BvashrNode(AbstractNode* expr1, AbstractNode* expr2);
        BvashrNode(const BvashrNode& copy);
        virtual ~BvashrNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(_ BitVec x)` node
    class BvdeclNode : public AbstractNode {
      public:
        BvdeclNode(triton::uint32 size);
        BvdeclNode(const BvdeclNode& copy);
        virtual ~BvdeclNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvlshr <expr1> <expr2>)` node
    class BvlshrNode : public AbstractNode {
      public:
        BvlshrNode(AbstractNode* expr1, AbstractNode* expr2);
        BvlshrNode(const BvlshrNode& copy);
        virtual ~BvlshrNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvmul <expr1> <expr2>)` node
    class BvmulNode : public AbstractNode {
      public:
        BvmulNode(AbstractNode* expr1, AbstractNode* expr2);
        BvmulNode(const BvmulNode& copy);
        virtual ~BvmulNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnand <expr1> <expr2>)` node
    class BvnandNode : public AbstractNode {
      public:
        BvnandNode(AbstractNode* expr1, AbstractNode* expr2);
        BvnandNode(const BvnandNode& copy);
        virtual ~BvnandNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvneg <expr>)` node
    class BvnegNode : public AbstractNode {
      public:
        BvnegNode(AbstractNode* expr);
        BvnegNode(const BvnegNode& copy);
        virtual ~BvnegNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnor <expr1> <expr2>)` node
    class BvnorNode : public AbstractNode {
      public:
        BvnorNode(AbstractNode* expr1, AbstractNode* expr2);
        BvnorNode(const BvnorNode& copy);
        virtual ~BvnorNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvnot <expr>)` node
    class BvnotNode : public AbstractNode {
      public:
        BvnotNode(AbstractNode* expr1);
        BvnotNode(const BvnotNode& copy);
        virtual ~BvnotNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvor <expr1> <expr2>)` node
    class BvorNode : public AbstractNode {
      public:
        BvorNode(AbstractNode* expr1, AbstractNode* expr2);
        BvorNode(const BvorNode& copy);
        virtual ~BvorNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ rotate_left rot) <expr>)` node
    class BvrolNode : public AbstractNode {
      public:
        BvrolNode(triton::uint32 rot, AbstractNode* expr);
        BvrolNode(AbstractNode* rot, AbstractNode* expr);
        BvrolNode(const BvrolNode& copy);
        virtual ~BvrolNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ rotate_right rot) <expr>)` node
    class BvrorNode : public AbstractNode {
      public:
        BvrorNode(triton::uint32 rot, AbstractNode* expr);
        BvrorNode(AbstractNode* rot, AbstractNode* expr);
        BvrorNode(const BvrorNode& copy);
        virtual ~BvrorNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsdiv <expr1> <expr2>)` node
    class BvsdivNode : public AbstractNode {
      public:
        BvsdivNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsdivNode(const BvsdivNode& copy);
        virtual ~BvsdivNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsge <expr1> <expr2>)` node
    class BvsgeNode : public AbstractNode {
      public:
        BvsgeNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsgeNode(const BvsgeNode& copy);
        virtual ~BvsgeNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsgt <expr1> <expr2>)` node
    class BvsgtNode : public AbstractNode {
      public:
        BvsgtNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsgtNode(const BvsgtNode& copy);
        virtual ~BvsgtNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvshl <expr1> <expr2>)` node
    class BvshlNode : public AbstractNode {
      public:
        BvshlNode(AbstractNode* expr1, AbstractNode* expr2);
        BvshlNode(const BvshlNode& copy);
        virtual ~BvshlNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsle <expr1> <expr2>)` node
    class BvsleNode : public AbstractNode {
      public:
        BvsleNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsleNode(const BvsleNode& copy);
        virtual ~BvsleNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvslt <expr1> <expr2>)` node
    class BvsltNode : public AbstractNode {
      public:
        BvsltNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsltNode(const BvsltNode& copy);
        virtual ~BvsltNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsmod <expr1> <expr2>)` node
    class BvsmodNode : public AbstractNode {
      public:
        BvsmodNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsmodNode(const BvsmodNode& copy);
        virtual ~BvsmodNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsrem <expr1> <expr2>)` node
    class BvsremNode : public AbstractNode {
      public:
        BvsremNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsremNode(const BvsremNode& copy);
        virtual ~BvsremNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvsub <expr1> <expr2>)` node
    class BvsubNode : public AbstractNode {
      public:
        BvsubNode(AbstractNode* expr1, AbstractNode* expr2);
        BvsubNode(const BvsubNode& copy);
        virtual ~BvsubNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvudiv <expr1> <expr2>)` node
    class BvudivNode : public AbstractNode {
      public:
        BvudivNode(AbstractNode* expr1, AbstractNode* expr2);
        BvudivNode(const BvudivNode& copy);
        virtual ~BvudivNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvuge <expr1> <expr2>)` node
    class BvugeNode : public AbstractNode {
      public:
        BvugeNode(AbstractNode* expr1, AbstractNode* expr2);
        BvugeNode(const BvugeNode& copy);
        virtual ~BvugeNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvugt <expr1> <expr2>)` node
    class BvugtNode : public AbstractNode {
      public:
        BvugtNode(AbstractNode* expr1, AbstractNode* expr2);
        BvugtNode(const BvugtNode& copy);
        virtual ~BvugtNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvule <expr1> <expr2>)` node
    class BvuleNode : public AbstractNode {
      public:
        BvuleNode(AbstractNode* expr1, AbstractNode* expr2);
        BvuleNode(const BvuleNode& copy);
        virtual ~BvuleNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvult <expr1> <expr2>)` node
    class BvultNode : public AbstractNode {
      public:
        BvultNode(AbstractNode* expr1, AbstractNode* expr2);
        BvultNode(const BvultNode& copy);
        virtual ~BvultNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvurem <expr1> <expr2>)` node
    class BvuremNode : public AbstractNode {
      public:
        BvuremNode(AbstractNode* expr1, AbstractNode* expr2);
        BvuremNode(const BvuremNode& copy);
        virtual ~BvuremNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvxnor <expr1> <expr2>)` node
    class BvxnorNode : public AbstractNode {
      public:
        BvxnorNode(AbstractNode* expr1, AbstractNode* expr2);
        BvxnorNode(const BvxnorNode& copy);
        virtual ~BvxnorNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(bvxor <expr1> <expr2>)` node
    class BvxorNode : public AbstractNode {
      public:
        BvxorNode(AbstractNode* expr1, AbstractNode* expr2);
        BvxorNode(const BvxorNode& copy);
        virtual ~BvxorNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(_ bv<value> <size>)` node
    class BvNode : public AbstractNode {
      public:
        BvNode(triton::uint512 value, triton::uint32 size);
        BvNode(const BvNode& copy);
        virtual ~BvNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! compound node
    class CompoundNode : public AbstractNode {
      public:
        CompoundNode(std::vector<AbstractNode*> exprs);
        CompoundNode(const CompoundNode& copy);
        virtual ~CompoundNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(concat <expr1> <expr2> ...)` node
    class ConcatNode : public AbstractNode {
      public:
        ConcatNode(AbstractNode* expr1, AbstractNode* expr2);
        ConcatNode(std::vector<AbstractNode* > exprs);
        ConcatNode(std::list<AbstractNode* > exprs);
        ConcatNode(const ConcatNode& copy);
        virtual ~ConcatNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Decimal node
    class DecimalNode : public AbstractNode {
      protected:
        triton::uint512 value;

      public:
        DecimalNode(triton::uint512 value);
        DecimalNode(const DecimalNode& copy);
        virtual ~DecimalNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;

        triton::uint512 getValue(void);
    };


    //! `(declare-fun <name> () bvDecl)` node
    class DeclareFunctionNode : public AbstractNode {
      public:
        DeclareFunctionNode(std::string name, AbstractNode* bvDecl);
        DeclareFunctionNode(const DeclareFunctionNode& copy);
        virtual ~DeclareFunctionNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(distinct <expr1> <expr2> ...)` node
    class DistinctNode : public AbstractNode {
      public:
        DistinctNode(AbstractNode* expr1, AbstractNode* expr2);
        DistinctNode(const DistinctNode& copy);
        virtual ~DistinctNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(= <expr1> <expr2> ...)` node
    class EqualNode : public AbstractNode {
      public:
        EqualNode(AbstractNode* expr1, AbstractNode* expr2);
        EqualNode(const EqualNode& copy);
        virtual ~EqualNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `((_ extract <high> <low>) <expr>)` node
    class ExtractNode : public AbstractNode {
      public:
        ExtractNode(triton::uint32 high, triton::uint32 low, AbstractNode* expr);
        ExtractNode(const ExtractNode& copy);
        virtual ~ExtractNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(ite <ifExpr> <thenExpr> <elseExpr>)`
    class IteNode : public AbstractNode {
      public:
        IteNode(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr);
        IteNode(const IteNode& copy);
        virtual ~IteNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(and <expr1> <expr2>)`
    class LandNode : public AbstractNode {
      public:
        LandNode(AbstractNode* expr1, AbstractNode* expr2);
        LandNode(const LandNode& copy);
        virtual ~LandNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(let ((<alias> <expr2>)) <expr3>)`
    class LetNode : public AbstractNode {
      public:
        LetNode(std::string alias, AbstractNode* expr2, AbstractNode* expr3);
        LetNode(const LetNode& copy);
        virtual ~LetNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(lnot <expr>)`
    class LnotNode : public AbstractNode {
      public:
        LnotNode(AbstractNode* expr);
        LnotNode(const LnotNode& copy);
        virtual ~LnotNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! `(or <expr1> <expr2>)`
    class LorNode : public AbstractNode {
      public:
        LorNode(AbstractNode* expr1, AbstractNode* expr2);
        LorNode(const LorNode& copy);
        virtual ~LorNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Reference node
    class ReferenceNode : public AbstractNode {
      protected:
        triton::usize value;

      public:
        ReferenceNode(triton::usize value);
        ReferenceNode(const ReferenceNode& copy);
        virtual ~ReferenceNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;

        triton::usize getValue(void);
    };


    //! String node
    class StringNode : public AbstractNode {
      protected:
        std::string value;

      public:
        StringNode(std::string value);
        StringNode(const StringNode& copy);
        virtual ~StringNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;

        std::string getValue(void);
    };


    //! `((_ sign_extend sizeExt) <expr>)` node
    class SxNode : public AbstractNode {
      public:
        SxNode(triton::uint32 sizeExt, AbstractNode* expr);
        SxNode(const SxNode& copy);
        virtual ~SxNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Variable node
    class VariableNode : public AbstractNode {
      protected:
        std::string value;

      public:
        VariableNode(triton::engines::symbolic::SymbolicVariable& symVar);
        VariableNode(const VariableNode& copy);
        virtual ~VariableNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;

        std::string getValue(void);
    };


    //! `((_ zero_extend sizeExt) <expr>)` node
    class ZxNode : public AbstractNode {
      public:
        ZxNode(triton::uint32 sizeExt, AbstractNode* expr);
        ZxNode(const ZxNode& copy);
        virtual ~ZxNode();
        virtual void init(void);
        virtual void accept(AstVisitor& v);
        virtual triton::uint512 hash(triton::uint32 deep) const;
    };


    //! Displays the node in ast representation.
    std::ostream& operator<<(std::ostream& stream, AbstractNode* node);

    //! AST C++ API - bv node builder
    AbstractNode* bv(triton::uint512 value, triton::uint32 size);

    //! AST C++ API - bvadd node builder
    AbstractNode* bvadd(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvand node builder
    AbstractNode* bvand(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvashr node builder
    AbstractNode* bvashr(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvdecl node builder
    AbstractNode* bvdecl(triton::uint32 size);

    //! AST C++ API - bvfalse node builder
    AbstractNode* bvfalse(void);

    //! AST C++ API - bvlshr node builder
    AbstractNode* bvlshr(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvmul node builder
    AbstractNode* bvmul(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvnand node builder
    AbstractNode* bvnand(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvneg node builder
    AbstractNode* bvneg(AbstractNode* expr);

    //! AST C++ API - bvnor node builder
    AbstractNode* bvnor(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvnot node builder
    AbstractNode* bvnot(AbstractNode* expr);

    //! AST C++ API - bvor node builder
    AbstractNode* bvor(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvrol node builder
    AbstractNode* bvrol(triton::uint32 rot, AbstractNode* expr);

    //! AST C++ API - bvrol node builder
    AbstractNode* bvrol(AbstractNode* rot, AbstractNode* expr);

    //! AST C++ API - bvror node builder
    AbstractNode* bvror(triton::uint32 rot, AbstractNode* expr);

    //! AST C++ API - bvror node builder
    AbstractNode* bvror(AbstractNode* rot, AbstractNode* expr);

    //! AST C++ API - bvsdiv node builder
    AbstractNode* bvsdiv(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvsge node builder
    AbstractNode* bvsge(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvsgt node builder
    AbstractNode* bvsgt(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvshl node builder
    AbstractNode* bvshl(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvsle node builder
    AbstractNode* bvsle(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvslt node builder
    AbstractNode* bvslt(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvsmod node builder
    AbstractNode* bvsmod(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvsrem node builder
    AbstractNode* bvsrem(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvsub node builder
    AbstractNode* bvsub(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvtrue node builder
    AbstractNode* bvtrue(void);

    //! AST C++ API - bvudiv node builder
    AbstractNode* bvudiv(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvuge node builder
    AbstractNode* bvuge(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvugt node builder
    AbstractNode* bvugt(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvule node builder
    AbstractNode* bvule(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvult node builder
    AbstractNode* bvult(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvurem node builder
    AbstractNode* bvurem(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvxnor node builder
    AbstractNode* bvxnor(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - bvxor node builder
    AbstractNode* bvxor(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - compound node builder
    AbstractNode* compound(std::vector<AbstractNode* > exprs);

    //! AST C++ API - concat node builder
    AbstractNode* concat(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - concat node builder
    AbstractNode* concat(std::vector<AbstractNode* > exprs);

    //! AST C++ API - concat node builder
    AbstractNode* concat(std::list<AbstractNode* > exprs);

    //! AST C++ API - decimal node builder
    AbstractNode* decimal(triton::uint512 value);

    //! AST C++ API - declare node builder
    AbstractNode* declareFunction(std::string name, AbstractNode* bvDecl);

    //! AST C++ API - distinct node builder
    AbstractNode* distinct(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - equal node builder
    AbstractNode* equal(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - extract node builder
    AbstractNode* extract(triton::uint32 high, triton::uint32 low, AbstractNode* expr);

    //! AST C++ API - ite node builder
    AbstractNode* ite(AbstractNode* ifExpr, AbstractNode* thenExpr, AbstractNode* elseExpr);

    //! AST C++ API - land node builder
    AbstractNode* land(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - let node builder
    AbstractNode* let(std::string alias, AbstractNode* expr2, AbstractNode* expr3);

    //! AST C++ API - lnot node builder
    AbstractNode* lnot(AbstractNode* expr);

    //! AST C++ API - lor node builder
    AbstractNode* lor(AbstractNode* expr1, AbstractNode* expr2);

    //! AST C++ API - reference node builder
    AbstractNode* reference(triton::usize value);

    //! AST C++ API - assert node builder
    AbstractNode* assert_(AbstractNode* expr);

    //! AST C++ API - string node builder
    AbstractNode* string(std::string value);

    //! AST C++ API - sx node builder
    AbstractNode* sx(triton::uint32 sizeExt, AbstractNode* expr);

    //! AST C++ API - variable node builder
    AbstractNode* variable(triton::engines::symbolic::SymbolicVariable& symVar);

    //! AST C++ API - zx node builder
    AbstractNode* zx(triton::uint32 sizeExt, AbstractNode* expr);

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
