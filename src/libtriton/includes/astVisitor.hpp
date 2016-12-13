//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTVISITOR_H
#define TRITON_ASTVISITOR_H



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

    class AssertNode;
    class BvaddNode;
    class BvandNode;
    class BvashrNode;
    class BvdeclNode;
    class BvlshrNode;
    class BvmulNode;
    class BvnandNode;
    class BvnegNode;
    class BvnorNode;
    class BvnotNode;
    class BvorNode;
    class BvrolNode;
    class BvrorNode;
    class BvsdivNode;
    class BvsgeNode;
    class BvsgtNode;
    class BvshlNode;
    class BvsleNode;
    class BvsltNode;
    class BvsmodNode;
    class BvsremNode;
    class BvsubNode;
    class BvudivNode;
    class BvugeNode;
    class BvugtNode;
    class BvuleNode;
    class BvultNode;
    class BvuremNode;
    class BvxnorNode;
    class BvxorNode;
    class BvNode;
    class CompoundNode;
    class ConcatNode;
    class DecimalNode;
    class DeclareFunctionNode;
    class DistinctNode;
    class EqualNode;
    class ExtractNode;
    class IteNode;
    class LandNode;
    class LetNode;
    class LnotNode;
    class LorNode;
    class ReferenceNode;
    class StringNode;
    class SxNode;
    class VariableNode;
    class ZxNode;

    //! \interface AstVisitor
    /*! \brief This interface is used to go through the ast AST. */
    class AstVisitor {
      public:
        AstVisitor(){};
        virtual ~AstVisitor(){};

        virtual void operator()(AssertNode& e) = 0;
        virtual void operator()(BvaddNode& e) = 0;
        virtual void operator()(BvandNode& e) = 0;
        virtual void operator()(BvashrNode& e) = 0;
        virtual void operator()(BvdeclNode& e) = 0;
        virtual void operator()(BvlshrNode& e) = 0;
        virtual void operator()(BvmulNode& e) = 0;
        virtual void operator()(BvnandNode& e) = 0;
        virtual void operator()(BvnegNode& e) = 0;
        virtual void operator()(BvnorNode& e) = 0;
        virtual void operator()(BvnotNode& e) = 0;
        virtual void operator()(BvorNode& e) = 0;
        virtual void operator()(BvrolNode& e) = 0;
        virtual void operator()(BvrorNode& e) = 0;
        virtual void operator()(BvsdivNode& e) = 0;
        virtual void operator()(BvsgeNode& e) = 0;
        virtual void operator()(BvsgtNode& e) = 0;
        virtual void operator()(BvshlNode& e) = 0;
        virtual void operator()(BvsleNode& e) = 0;
        virtual void operator()(BvsltNode& e) = 0;
        virtual void operator()(BvsmodNode& e) = 0;
        virtual void operator()(BvsremNode& e) = 0;
        virtual void operator()(BvsubNode& e) = 0;
        virtual void operator()(BvudivNode& e) = 0;
        virtual void operator()(BvugeNode& e) = 0;
        virtual void operator()(BvugtNode& e) = 0;
        virtual void operator()(BvuleNode& e) = 0;
        virtual void operator()(BvultNode& e) = 0;
        virtual void operator()(BvuremNode& e) = 0;
        virtual void operator()(BvxnorNode& e) = 0;
        virtual void operator()(BvxorNode& e) = 0;
        virtual void operator()(BvNode& e) = 0;
        virtual void operator()(CompoundNode& e) = 0;
        virtual void operator()(ConcatNode& e) = 0;
        virtual void operator()(DecimalNode& e) = 0;
        virtual void operator()(DeclareFunctionNode& e) = 0;
        virtual void operator()(DistinctNode& e) = 0;
        virtual void operator()(EqualNode& e) = 0;
        virtual void operator()(ExtractNode& e) = 0;
        virtual void operator()(IteNode& e) = 0;
        virtual void operator()(LandNode& e) = 0;
        virtual void operator()(LetNode& e) = 0;
        virtual void operator()(LnotNode& e) = 0;
        virtual void operator()(LorNode& e) = 0;
        virtual void operator()(ReferenceNode& e) = 0;
        virtual void operator()(StringNode& e) = 0;
        virtual void operator()(SxNode& e) = 0;
        virtual void operator()(VariableNode& e) = 0;
        virtual void operator()(ZxNode& e) = 0;
    }; /* AstVisitor class */

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTVISITOR_H */

