//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SMT2LIB_H
#define TRITON_SMT2LIB_H

#include <list>
#include <map>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "smt2libVisitor.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The SMT2-Lib namespace
  namespace smt2lib {
  /*!
   *  \ingroup triton
   *  \addtogroup smt2-lib
   *  @{
   */

    /*! Enumerates all kinds of node. Must be prime numbers. */
    enum kind_e {
      UNDEFINED_NODE = 0,     /*!< Unknown node */
      ASSERT_NODE = 2,        /*!< (assert x) */
      BVADD_NODE = 3,         /*!< (bvadd x y) */
      BVAND_NODE = 5,         /*!< (bvand x y) */
      BVASHR_NODE = 7,        /*!< (bvashr x y) */
      BVLSHR_NODE = 11,       /*!< (bvlshr x y) */
      BVMUL_NODE = 13,        /*!< (bvmul x y) */
      BVNAND_NODE = 17,       /*!< (bvnand x y) */
      BVNEG_NODE = 19,        /*!< (bvneg x) */
      BVNOR_NODE = 23,        /*!< (bvnor x y) */
      BVNOT_NODE = 29,        /*!< (bvnot x) */
      BVOR_NODE = 31,         /*!< (bvor x y) */
      BVROL_NODE = 37,        /*!< ((_ rotate_left x) y) */
      BVROR_NODE = 41,        /*!< ((_ rotate_right x) y) */
      BVSDIV_NODE = 43,       /*!< (bvsdiv x y) */
      BVSGE_NODE = 47,        /*!< (bvsge x y) */
      BVSGT_NODE = 53,        /*!< (bvsgt x y) */
      BVSHL_NODE = 59,        /*!< (bvshl x y) */
      BVSLE_NODE = 61,        /*!< (bvslr x y) */
      BVSLT_NODE = 67,        /*!< (bvslt x y) */
      BVSMOD_NODE = 71,       /*!< (bvsmod x y) */
      BVSREM_NODE = 73,       /*!< (bvsrem x y) */
      BVSUB_NODE = 79,        /*!< (bvsub x y) */
      BVUDIV_NODE = 83,       /*!< (bvudiv x y) */
      BVUGE_NODE = 89,        /*!< (bvuge x y) */
      BVUGT_NODE = 97,        /*!< (bvugt x y) */
      BVULE_NODE = 101,       /*!< (bvule x y) */
      BVULT_NODE = 103,       /*!< (bvult x y) */
      BVUREM_NODE = 107,      /*!< (bvurem x y) */
      BVXNOR_NODE = 109,      /*!< (bvxnor x y) */
      BVXOR_NODE = 113,       /*!< (bvxor x y) */
      BV_NODE = 127,          /*!< (_ bvx y) */
      COMPOUND_NODE = 131,    /*!< Coumpound of several nodes */
      CONCAT_NODE = 139,      /*!< (concat x y z ...) */
      DECIMAL_NODE = 149,     /*!< Decimal node */
      DECLARE_NODE = 151,     /*!< (declare-fun x () (_ BitVec y)) */
      DISTINCT_NODE = 157,    /*!< (distinct x y) */
      EQUAL_NODE = 163,       /*!< (= x y) */
      EXTRACT_NODE = 167,     /*!< ((_ extract x y) z) */
      ITE_NODE = 173,         /*!< (ite x y z) */
      LAND_NODE = 179,        /*!< (and x y) */
      LNOT_NODE = 181,        /*!< (and x y) */
      LOR_NODE = 191,         /*!< (or x y) */
      REFERENCE_NODE = 193,   /*!< Reference node */
      STRING_NODE = 197,      /*!< String node */
      SX_NODE = 199,          /*!< ((_ sign_extend x) y) */
      VARIABLE_NODE = 211,    /*!< Variable node */
      ZX_NODE = 223           /*!< ((_ zero_extend x) y) */
    };


    //! Abstract node
    class smtAstAbstractNode
    {
      protected:
        //! The node's kind.
        enum kind_e kind;

        //! The node's childs.
        std::vector<smtAstAbstractNode*> childs;

      public:
        //! Constructor.
        smtAstAbstractNode(enum kind_e kind);

        //! Constructor by copy.
        smtAstAbstractNode(const smtAstAbstractNode& copy);

        //! Constructor.
        smtAstAbstractNode();

        //! Destructor.
        virtual ~smtAstAbstractNode();

        //! Returns the node's kind.
        enum kind_e getKind(void);

        //! Returns the expression's size.
        triton::uint32 getBitvectorSize(void);

        //! Returns the node's childs.
        std::vector<smtAstAbstractNode*>& getChilds(void);

        //! Adds a child.
        void addChild(smtAstAbstractNode* child);

        //! Entry point for a visitor.
        virtual void accept(Visitor& v) = 0;

        //! Returns the graph's hash. The hash is computed recursively on the whole graph.
        virtual triton::uint512 hash(triton::uint32 deep) = 0;
    };


    //! (assert <expr1>) node
    class smtAstAssertNode : public smtAstAbstractNode
    {
      public:
        smtAstAssertNode(smtAstAbstractNode* expr);
        smtAstAssertNode(const smtAstAssertNode& copy);
        ~smtAstAssertNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvadd <expr1> <expr2>) node
    class smtAstBvaddNode : public smtAstAbstractNode
    {
      public:
        smtAstBvaddNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvaddNode(const smtAstBvaddNode& copy);
        ~smtAstBvaddNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvand <expr1> <expr2>) node
    class smtAstBvandNode : public smtAstAbstractNode
    {
      public:
        smtAstBvandNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvandNode(const smtAstBvandNode& copy);
        ~smtAstBvandNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvashr <expr1> <expr2>) node
    class smtAstBvashrNode : public smtAstAbstractNode
    {
      public:
        smtAstBvashrNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvashrNode(const smtAstBvashrNode& copy);
        ~smtAstBvashrNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvlshr <expr1> <expr2>) node
    class smtAstBvlshrNode : public smtAstAbstractNode
    {
      public:
        smtAstBvlshrNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvlshrNode(const smtAstBvlshrNode& copy);
        ~smtAstBvlshrNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvmul <expr1> <expr2>) node
    class smtAstBvmulNode : public smtAstAbstractNode
    {
      public:
        smtAstBvmulNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvmulNode(const smtAstBvmulNode& copy);
        ~smtAstBvmulNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvnand <expr1> <expr2>) node
    class smtAstBvnandNode : public smtAstAbstractNode
    {
      public:
        smtAstBvnandNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvnandNode(const smtAstBvnandNode& copy);
        ~smtAstBvnandNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvneg <expr>) node
    class smtAstBvnegNode : public smtAstAbstractNode
    {
      public:
        smtAstBvnegNode(smtAstAbstractNode* expr);
        smtAstBvnegNode(const smtAstBvnegNode& copy);
        ~smtAstBvnegNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvnor <expr1> <expr2>) node
    class smtAstBvnorNode : public smtAstAbstractNode
    {
      public:
        smtAstBvnorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvnorNode(const smtAstBvnorNode& copy);
        ~smtAstBvnorNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvnot <expr>) node
    class smtAstBvnotNode : public smtAstAbstractNode
    {
      public:
        smtAstBvnotNode(smtAstAbstractNode* expr1);
        smtAstBvnotNode(const smtAstBvnotNode& copy);
        ~smtAstBvnotNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvor <expr1> <expr2>) node
    class smtAstBvorNode : public smtAstAbstractNode
    {
      public:
        smtAstBvorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvorNode(const smtAstBvorNode& copy);
        ~smtAstBvorNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! ((_ rotate_left rot) expr) node
    class smtAstBvrolNode : public smtAstAbstractNode
    {
      public:
        smtAstBvrolNode(triton::uint32 rot, smtAstAbstractNode* expr);
        smtAstBvrolNode(smtAstAbstractNode* rot, smtAstAbstractNode* expr);
        smtAstBvrolNode(const smtAstBvrolNode& copy);
        ~smtAstBvrolNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! ((_ rotate_right rot) expr) node
    class smtAstBvrorNode : public smtAstAbstractNode
    {
      public:
        smtAstBvrorNode(triton::uint32 rot, smtAstAbstractNode* expr);
        smtAstBvrorNode(smtAstAbstractNode* rot, smtAstAbstractNode* expr);
        smtAstBvrorNode(const smtAstBvrorNode& copy);
        ~smtAstBvrorNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsdiv <expr1> <expr2>) node
    class smtAstBvsdivNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsdivNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsdivNode(const smtAstBvsdivNode& copy);
        ~smtAstBvsdivNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsge <expr1> <expr2>) node
    class smtAstBvsgeNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsgeNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsgeNode(const smtAstBvsgeNode& copy);
        ~smtAstBvsgeNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsgt <expr1> <expr2>) node
    class smtAstBvsgtNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsgtNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsgtNode(const smtAstBvsgtNode& copy);
        ~smtAstBvsgtNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvshl <expr1> <expr2>) node
    class smtAstBvshlNode : public smtAstAbstractNode
    {
      public:
        smtAstBvshlNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvshlNode(const smtAstBvshlNode& copy);
        ~smtAstBvshlNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsle <expr1> <expr2>) node
    class smtAstBvsleNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsleNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsleNode(const smtAstBvsleNode& copy);
        ~smtAstBvsleNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvslt <expr1> <expr2>) node
    class smtAstBvsltNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsltNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsltNode(const smtAstBvsltNode& copy);
        ~smtAstBvsltNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsmod <expr1> <expr2>) node
    class smtAstBvsmodNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsmodNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsmodNode(const smtAstBvsmodNode& copy);
        ~smtAstBvsmodNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsrem <expr1> <expr2>) node
    class smtAstBvsremNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsremNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsremNode(const smtAstBvsremNode& copy);
        ~smtAstBvsremNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvsub <expr1> <expr2>) node
    class smtAstBvsubNode : public smtAstAbstractNode
    {
      public:
        smtAstBvsubNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvsubNode(const smtAstBvsubNode& copy);
        ~smtAstBvsubNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvudiv <expr1> <expr2>) node
    class smtAstBvudivNode : public smtAstAbstractNode
    {
      public:
        smtAstBvudivNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvudivNode(const smtAstBvudivNode& copy);
        ~smtAstBvudivNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvuge <expr1> <expr2>) node
    class smtAstBvugeNode : public smtAstAbstractNode
    {
      public:
        smtAstBvugeNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvugeNode(const smtAstBvugeNode& copy);
        ~smtAstBvugeNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvugt <expr1> <expr2>) node
    class smtAstBvugtNode : public smtAstAbstractNode
    {
      public:
        smtAstBvugtNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvugtNode(const smtAstBvugtNode& copy);
        ~smtAstBvugtNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvule <expr1> <expr2>) node
    class smtAstBvuleNode : public smtAstAbstractNode
    {
      public:
        smtAstBvuleNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvuleNode(const smtAstBvuleNode& copy);
        ~smtAstBvuleNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvult <expr1> <expr2>) node
    class smtAstBvultNode : public smtAstAbstractNode
    {
      public:
        smtAstBvultNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvultNode(const smtAstBvultNode& copy);
        ~smtAstBvultNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvurem <expr1> <expr2>) node
    class smtAstBvuremNode : public smtAstAbstractNode
    {
      public:
        smtAstBvuremNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvuremNode(const smtAstBvuremNode& copy);
        ~smtAstBvuremNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvxnor <expr1> <expr2>) node
    class smtAstBvxnorNode : public smtAstAbstractNode
    {
      public:
        smtAstBvxnorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvxnorNode(const smtAstBvxnorNode& copy);
        ~smtAstBvxnorNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (bvxor <expr1> <expr2>) node
    class smtAstBvxorNode : public smtAstAbstractNode
    {
      public:
        smtAstBvxorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstBvxorNode(const smtAstBvxorNode& copy);
        ~smtAstBvxorNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (_ bv<value> <size>) node
    class smtAstBvNode : public smtAstAbstractNode
    {
      public:
        smtAstBvNode(triton::uint128 value, triton::uint32 size);
        smtAstBvNode(const smtAstBvNode& copy);
        ~smtAstBvNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! compound node
    class smtAstCompoundNode : public smtAstAbstractNode
    {
      public:
        smtAstCompoundNode(std::vector<smtAstAbstractNode*> exprs);
        smtAstCompoundNode(const smtAstCompoundNode& copy);
        ~smtAstCompoundNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (concat <expr1> <expr2> ...) node
    class smtAstConcatNode : public smtAstAbstractNode
    {
      public:
        smtAstConcatNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstConcatNode(std::vector<smtAstAbstractNode* > exprs);
        smtAstConcatNode(std::list<smtAstAbstractNode* > exprs);
        smtAstConcatNode(const smtAstConcatNode& copy);
        ~smtAstConcatNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! Decimal node
    class smtAstDecimalNode : public smtAstAbstractNode
    {
      protected:
        triton::uint128 value;

      public:
        smtAstDecimalNode(triton::uint128 value);
        smtAstDecimalNode(const smtAstDecimalNode& copy);
        ~smtAstDecimalNode();

        triton::uint128 getValue(void);
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (declare-fun <symVarName> () (_ BitVec <symVarSize>)) node
    class smtAstDeclareNode : public smtAstAbstractNode
    {
      public:
        smtAstDeclareNode(std::string symVarName, triton::uint32 symVarSize);
        smtAstDeclareNode(const smtAstDeclareNode& copy);
        ~smtAstDeclareNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };

    //! (distinct <expr1> <expr2> ...) node
    class smtAstDistinctNode : public smtAstAbstractNode
    {
      public:
        smtAstDistinctNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstDistinctNode(const smtAstDistinctNode& copy);
        ~smtAstDistinctNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (= <expr1> <expr2> ...) node
    class smtAstEqualNode : public smtAstAbstractNode
    {
      public:
        smtAstEqualNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstEqualNode(const smtAstEqualNode& copy);
        ~smtAstEqualNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! ((_ extract <high> <low>) <expr>) node
    class smtAstExtractNode : public smtAstAbstractNode
    {
      public:
        smtAstExtractNode(triton::uint32 high, triton::uint32 low, smtAstAbstractNode* expr);
        smtAstExtractNode(const smtAstExtractNode& copy);
        ~smtAstExtractNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (ite ifExpr thenExpr elseExpr)
    class smtAstIteNode : public smtAstAbstractNode
    {
      public:
        smtAstIteNode(smtAstAbstractNode* ifExpr, smtAstAbstractNode* thenExpr, smtAstAbstractNode* elseExpr);
        smtAstIteNode(const smtAstIteNode& copy);
        ~smtAstIteNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (and <expr1> <expr2>)
    class smtAstLandNode : public smtAstAbstractNode
    {
      public:
        smtAstLandNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstLandNode(const smtAstLandNode& copy);
        ~smtAstLandNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (lnot <expr>)
    class smtAstLnotNode : public smtAstAbstractNode
    {
      public:
        smtAstLnotNode(smtAstAbstractNode* expr);
        smtAstLnotNode(const smtAstLnotNode& copy);
        ~smtAstLnotNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! (or <expr1> <expr2>)
    class smtAstLorNode : public smtAstAbstractNode
    {
      public:
        smtAstLorNode(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);
        smtAstLorNode(const smtAstLorNode& copy);
        ~smtAstLorNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! Reference node
    class smtAstReferenceNode : public smtAstAbstractNode
    {
      protected:
        triton::__uint value;

      public:
        smtAstReferenceNode(triton::__uint value);
        smtAstReferenceNode(const smtAstReferenceNode& copy);
        ~smtAstReferenceNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);

        triton::__uint getValue(void);
    };


    //! String node
    class smtAstStringNode : public smtAstAbstractNode
    {
      protected:
        std::string value;

      public:
        smtAstStringNode(std::string value);
        smtAstStringNode(const smtAstStringNode& copy);
        ~smtAstStringNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);

        std::string getValue(void);
    };


    //! ((_ sign_extend sizeExt) <expr>) node
    class smtAstSxNode : public smtAstAbstractNode
    {
      public:
        smtAstSxNode(triton::uint32 sizeExt, smtAstAbstractNode* expr);
        smtAstSxNode(const smtAstSxNode& copy);
        ~smtAstSxNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! Variable node
    class smtAstVariableNode : public smtAstAbstractNode
    {
      protected:
        std::string value;

      public:
        smtAstVariableNode(std::string value);
        smtAstVariableNode(const smtAstVariableNode& copy);
        ~smtAstVariableNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);

        std::string getValue(void);
    };


    //! ((_ zero_extend sizeExt) <expr>) node
    class smtAstZxNode : public smtAstAbstractNode
    {
      public:
        smtAstZxNode(triton::uint32 sizeExt, smtAstAbstractNode* expr);
        smtAstZxNode(const smtAstZxNode& copy);
        ~smtAstZxNode();
        virtual void accept(Visitor& v);
        virtual triton::uint512 hash(triton::uint32 deep);
    };


    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstAbstractNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstAssertNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvaddNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvandNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvashrNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvlshrNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvmulNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvnandNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvnegNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvnorNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvnotNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvorNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvrolNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvrorNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsdivNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsgeNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsgtNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvshlNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsleNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsltNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsmodNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsremNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvsubNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvudivNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvugeNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvugtNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvuleNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvultNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvuremNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvxnorNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstBvxorNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstCompoundNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstConcatNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstDecimalNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstDeclareNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstDistinctNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstEqualNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstExtractNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstIteNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstLandNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstLnotNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstLorNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstReferenceNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstStringNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstSxNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstVariableNode* node);

    //! Displays the node in smt2-lib syntax.
    std::ostream& operator<<(std::ostream& stream, smtAstZxNode* node);

    //! Compares two trees.
    bool operator==(smtAstAbstractNode& node1, smtAstAbstractNode& node2);


    //! smt2-lib C++ api - bv node builder
    smtAstAbstractNode* bv(triton::uint128 value, triton::uint32 size);

    //! smt2-lib C++ api - bvadd node builder
    smtAstAbstractNode* bvadd(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvand node builder
    smtAstAbstractNode* bvand(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvashr node builder
    smtAstAbstractNode* bvashr(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvfalse node builder
    smtAstAbstractNode* bvfalse(void);

    //! smt2-lib C++ api - bvlshr node builder
    smtAstAbstractNode* bvlshr(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvmul node builder
    smtAstAbstractNode* bvmul(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvnand node builder
    smtAstAbstractNode* bvnand(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvneg node builder
    smtAstAbstractNode* bvneg(smtAstAbstractNode* expr);

    //! smt2-lib C++ api - bvnor node builder
    smtAstAbstractNode* bvnor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvnot node builder
    smtAstAbstractNode* bvnot(smtAstAbstractNode* expr);

    //! smt2-lib C++ api - bvor node builder
    smtAstAbstractNode* bvor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvrol node builder
    smtAstAbstractNode* bvrol(triton::uint32 rot, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - bvrol node builder
    smtAstAbstractNode* bvrol(smtAstAbstractNode* rot, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - bvror node builder
    smtAstAbstractNode* bvror(triton::uint32 rot, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - bvror node builder
    smtAstAbstractNode* bvror(smtAstAbstractNode* rot, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - bvsdiv node builder
    smtAstAbstractNode* bvsdiv(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvsge node builder
    smtAstAbstractNode* bvsge(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvsgt node builder
    smtAstAbstractNode* bvsgt(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvshl node builder
    smtAstAbstractNode* bvshl(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvsle node builder
    smtAstAbstractNode* bvsle(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvslt node builder
    smtAstAbstractNode* bvslt(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvsmod node builder
    smtAstAbstractNode* bvsmod(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvsrem node builder
    smtAstAbstractNode* bvsrem(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvsub node builder
    smtAstAbstractNode* bvsub(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvtrue node builder
    smtAstAbstractNode* bvtrue(void);

    //! smt2-lib C++ api - bvudiv node builder
    smtAstAbstractNode* bvudiv(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvuge node builder
    smtAstAbstractNode* bvuge(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvugt node builder
    smtAstAbstractNode* bvugt(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvule node builder
    smtAstAbstractNode* bvule(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvult node builder
    smtAstAbstractNode* bvult(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvurem node builder
    smtAstAbstractNode* bvurem(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvxnor node builder
    smtAstAbstractNode* bvxnor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - bvxor node builder
    smtAstAbstractNode* bvxor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - compound node builder
    smtAstAbstractNode* compound(std::vector<smtAstAbstractNode* > exprs);

    //! smt2-lib C++ api - concat node builder
    smtAstAbstractNode* concat(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - concat node builder
    smtAstAbstractNode* concat(std::vector<smtAstAbstractNode* > exprs);

    //! smt2-lib C++ api - concat node builder
    smtAstAbstractNode* concat(std::list<smtAstAbstractNode* > exprs);

    //! smt2-lib C++ api - decimal node builder
    smtAstAbstractNode* decimal(triton::uint128 value);

    //! smt2-lib C++ api - declare node builder
    smtAstAbstractNode* declare(std::string symVarName, triton::uint32 symVarSize);

    //! smt2-lib C++ api - distinct node builder
    smtAstAbstractNode* distinct(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - equal node builder
    smtAstAbstractNode* equal(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - extract node builder
    smtAstAbstractNode* extract(triton::uint32 high, triton::uint32 low, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - ite node builder
    smtAstAbstractNode* ite(smtAstAbstractNode* ifExpr, smtAstAbstractNode* thenExpr, smtAstAbstractNode* elseExpr);

    //! smt2-lib C++ api - land node builder
    smtAstAbstractNode* land(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - lnot node builder
    smtAstAbstractNode* lnot(smtAstAbstractNode* expr);

    //! smt2-lib C++ api - lor node builder
    smtAstAbstractNode* lor(smtAstAbstractNode* expr1, smtAstAbstractNode* expr2);

    //! smt2-lib C++ api - reference node builder
    smtAstAbstractNode* reference(triton::__uint value);

    //! smt2-lib C++ api - smtAssert node builder
    smtAstAbstractNode* smtAssert(smtAstAbstractNode* expr);

    //! smt2-lib C++ api - string node builder
    smtAstAbstractNode* string(std::string value);

    //! smt2-lib C++ api - sx node builder
    smtAstAbstractNode* sx(triton::uint32 sizeExt, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - variable node builder
    smtAstAbstractNode* variable(std::string variable);

    //! smt2-lib C++ api - zx node builder
    smtAstAbstractNode* zx(triton::uint32 sizeExt, smtAstAbstractNode* expr);

    //! smt2-lib C++ api - Duplicates the AST
    smtAstAbstractNode* newInstance(smtAstAbstractNode* node);

    //! Garbage collector - This container contains all allocated nodes.
    extern std::set<smtAstAbstractNode*> allocatedNodes;

    //! Garbage collector - Go through every allocated nodes and free them.
    void freeAllAstNodes(void);

    //! Garbage collector - Frees a set of nodes and removes them from the global container.
    void freeAstNodes(std::set<smtAstAbstractNode*>& nodes);

    //! Garbage collector - Extracts all unique nodes from a partial AST into the `uniqueNodes` set.
    void extractUniqueAstNodes(std::set<smtAstAbstractNode*>& uniqueNodes, smtAstAbstractNode* root);

    //! Garbage collector - Records the allocated node or returns the same node if it already exists inside the summaries.
    smtAstAbstractNode* recordNode(smtAstAbstractNode* node);

    //! Custom pow function for hash routine.
    triton::uint512 pow(triton::uint512 hash, triton::uint32 n);

    //! Custom rotate left function for hash routine.
    triton::uint512 rotl(triton::uint512 value, triton::uint32 shift);

  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};


#endif /* TRITON_SMT2LIB_H */

