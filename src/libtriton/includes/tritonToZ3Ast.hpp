//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_TRITONTOZ3AST_H
#define TRITON_TRITONTOZ3AST_H

#include <z3++.h>

#include "ast.hpp"
#include "astVisitor.hpp"
#include "z3Result.hpp"
#include "tritonTypes.hpp"



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

    //! \class TritonToZ3Ast
    /*! \brief Converts a Triton's AST to Z3's AST. */
    class TritonToZ3Ast : public AstVisitor {

      private:
        //! This flag define if the conversion is used to evaluated a node or not.
        bool isEval;

        //! The map of symbols. E.g: (let (symbols expr1) expr2)
        std::map<std::string, triton::ast::smtAstAbstractNode*> symbols;

      protected:
        //! The result.
        Z3Result result;

      public:
        //! Constructor.
        TritonToZ3Ast(bool eval=true);

        //! Destructor.
        ~TritonToZ3Ast();

        //! Evaluates a Triton AST.
        virtual Z3Result& eval(triton::ast::smtAstAbstractNode& e);

        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstAbstractNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstAssertNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvaddNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvandNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvashrNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvdeclNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvlshrNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvmulNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsmodNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvnandNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvnegNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvnorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvnotNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvrolNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvrorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsdivNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsgeNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsgtNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvshlNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsleNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsltNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsremNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvsubNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvudivNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvugeNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvugtNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvuleNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvultNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvuremNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvxnorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvxorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstBvNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstCompoundNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstConcatNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstDecimalNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstDeclareFunctionNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstDistinctNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstEqualNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstExtractNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstIteNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstLandNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstLetNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstLnotNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstLorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstReferenceNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstStringNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstSxNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstVariableNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::smtAstZxNode& e);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOZ3AST_H */

