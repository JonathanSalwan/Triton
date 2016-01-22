//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_Z3AST_H
#define TRITON_Z3AST_H

#include <z3++.h>

#include "smt2lib.hpp"
#include "smt2libVisitor.hpp"
#include "smt2libZ3Result.hpp"
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

    //! \class Z3Ast
    /*! \brief Converts a Triton's AST to Z3's AST. */
    class Z3Ast : public Visitor {

      protected:
        //! The result.
        Z3Result result;

      public:
        //! Constructor.
        Z3Ast();

        //! Destructor.
        ~Z3Ast();

        //! Evaluates a Triton AST.
        virtual Z3Result& eval(smt2lib::smtAstAbstractNode& e);

        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstAbstractNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstAssertNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvaddNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvandNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvashrNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvlshrNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvmulNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsmodNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvnandNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvnegNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvnorNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvnotNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvorNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvrolNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvrorNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsdivNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsgeNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsgtNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvshlNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsleNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsltNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsremNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvsubNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvudivNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvugeNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvugtNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvuleNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvultNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvuremNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvxnorNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvxorNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstBvNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstCompoundNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstConcatNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstDecimalNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstDeclareNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstDistinctNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstEqualNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstExtractNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstIteNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstLandNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstLnotNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstLorNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstReferenceNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstStringNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstSxNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstVariableNode& e);
        //! Evaluate operator.
        virtual void operator()(smt2lib::smtAstZxNode& e);
    };

  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3AST_H */

