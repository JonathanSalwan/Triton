//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ASTVISITOR_H
#define TRITON_ASTVISITOR_H



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The SMT2-Lib namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    class smtAstAssertNode;
    class smtAstBvaddNode;
    class smtAstBvandNode;
    class smtAstBvashrNode;
    class smtAstBvdeclNode;
    class smtAstBvlshrNode;
    class smtAstBvmulNode;
    class smtAstBvnandNode;
    class smtAstBvnegNode;
    class smtAstBvnorNode;
    class smtAstBvnotNode;
    class smtAstBvorNode;
    class smtAstBvrolNode;
    class smtAstBvrorNode;
    class smtAstBvsdivNode;
    class smtAstBvsgeNode;
    class smtAstBvsgtNode;
    class smtAstBvshlNode;
    class smtAstBvsleNode;
    class smtAstBvsltNode;
    class smtAstBvsmodNode;
    class smtAstBvsremNode;
    class smtAstBvsubNode;
    class smtAstBvudivNode;
    class smtAstBvugeNode;
    class smtAstBvugtNode;
    class smtAstBvuleNode;
    class smtAstBvultNode;
    class smtAstBvuremNode;
    class smtAstBvxnorNode;
    class smtAstBvxorNode;
    class smtAstBvNode;
    class smtAstCompoundNode;
    class smtAstConcatNode;
    class smtAstDecimalNode;
    class smtAstDeclareFunctionNode;
    class smtAstDistinctNode;
    class smtAstEqualNode;
    class smtAstExtractNode;
    class smtAstIteNode;
    class smtAstLandNode;
    class smtAstLetNode;
    class smtAstLnotNode;
    class smtAstLorNode;
    class smtAstReferenceNode;
    class smtAstStringNode;
    class smtAstSxNode;
    class smtAstVariableNode;
    class smtAstZxNode;

    //! \interface AstVisitor
    /*! \brief This interface is used to go through the ast AST. */
    class AstVisitor {

      public:
        AstVisitor(){};
        virtual ~AstVisitor(){};

        virtual void operator()(smtAstAssertNode& e) = 0;
        virtual void operator()(smtAstBvaddNode& e) = 0;
        virtual void operator()(smtAstBvandNode& e) = 0;
        virtual void operator()(smtAstBvashrNode& e) = 0;
        virtual void operator()(smtAstBvdeclNode& e) = 0;
        virtual void operator()(smtAstBvlshrNode& e) = 0;
        virtual void operator()(smtAstBvmulNode& e) = 0;
        virtual void operator()(smtAstBvnandNode& e) = 0;
        virtual void operator()(smtAstBvnegNode& e) = 0;
        virtual void operator()(smtAstBvnorNode& e) = 0;
        virtual void operator()(smtAstBvnotNode& e) = 0;
        virtual void operator()(smtAstBvorNode& e) = 0;
        virtual void operator()(smtAstBvrolNode& e) = 0;
        virtual void operator()(smtAstBvrorNode& e) = 0;
        virtual void operator()(smtAstBvsdivNode& e) = 0;
        virtual void operator()(smtAstBvsgeNode& e) = 0;
        virtual void operator()(smtAstBvsgtNode& e) = 0;
        virtual void operator()(smtAstBvshlNode& e) = 0;
        virtual void operator()(smtAstBvsleNode& e) = 0;
        virtual void operator()(smtAstBvsltNode& e) = 0;
        virtual void operator()(smtAstBvsmodNode& e) = 0;
        virtual void operator()(smtAstBvsremNode& e) = 0;
        virtual void operator()(smtAstBvsubNode& e) = 0;
        virtual void operator()(smtAstBvudivNode& e) = 0;
        virtual void operator()(smtAstBvugeNode& e) = 0;
        virtual void operator()(smtAstBvugtNode& e) = 0;
        virtual void operator()(smtAstBvuleNode& e) = 0;
        virtual void operator()(smtAstBvultNode& e) = 0;
        virtual void operator()(smtAstBvuremNode& e) = 0;
        virtual void operator()(smtAstBvxnorNode& e) = 0;
        virtual void operator()(smtAstBvxorNode& e) = 0;
        virtual void operator()(smtAstBvNode& e) = 0;
        virtual void operator()(smtAstCompoundNode& e) = 0;
        virtual void operator()(smtAstConcatNode& e) = 0;
        virtual void operator()(smtAstDecimalNode& e) = 0;
        virtual void operator()(smtAstDeclareFunctionNode& e) = 0;
        virtual void operator()(smtAstDistinctNode& e) = 0;
        virtual void operator()(smtAstEqualNode& e) = 0;
        virtual void operator()(smtAstExtractNode& e) = 0;
        virtual void operator()(smtAstIteNode& e) = 0;
        virtual void operator()(smtAstLandNode& e) = 0;
        virtual void operator()(smtAstLetNode& e) = 0;
        virtual void operator()(smtAstLnotNode& e) = 0;
        virtual void operator()(smtAstLorNode& e) = 0;
        virtual void operator()(smtAstReferenceNode& e) = 0;
        virtual void operator()(smtAstStringNode& e) = 0;
        virtual void operator()(smtAstSxNode& e) = 0;
        virtual void operator()(smtAstVariableNode& e) = 0;
        virtual void operator()(smtAstZxNode& e) = 0;

    }; /* AstVisitor class */

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTVISITOR_H */

