//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TRITONTOZ3AST_H
#define TRITON_TRITONTOZ3AST_H

#include <z3++.h>

#include <triton/ast.hpp>
#include <triton/astVisitor.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/z3Result.hpp>



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

    //! \class TritonToZ3Ast
    /*! \brief Converts a Triton's AST to Z3's AST. */
    class TritonToZ3Ast : public AstVisitor {
      private:
        //! Symbolic Engine API
        triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        //! This flag define if the conversion is used to evaluated a node or not.
        bool isEval;

        //! The map of symbols. E.g: (let (symbols expr1) expr2)
        std::map<std::string, triton::ast::AbstractNode*> symbols;

      protected:
        //! The result.
        Z3Result result;

      public:
        //! Constructor.
        TritonToZ3Ast(triton::engines::symbolic::SymbolicEngine* symbolicEngine, bool eval=true);

        //! Destructor.
        virtual ~TritonToZ3Ast();

        //! Evaluates a Triton AST.
        virtual Z3Result& eval(triton::ast::AbstractNode& e);

        //! Evaluate operator.
        virtual void operator()(triton::ast::AbstractNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::AssertNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvaddNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvandNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvashrNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvdeclNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvlshrNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvmulNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsmodNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvnandNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvnegNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvnorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvnotNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvrolNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvrorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsdivNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsgeNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsgtNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvshlNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsleNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsltNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsremNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvsubNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvudivNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvugeNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvugtNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvuleNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvultNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvuremNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvxnorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvxorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::BvNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::CompoundNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::ConcatNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::DecimalNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::DeclareFunctionNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::DistinctNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::EqualNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::ExtractNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::IteNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::LandNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::LetNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::LnotNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::LorNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::ReferenceNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::StringNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::SxNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::VariableNode& e);
        //! Evaluate operator.
        virtual void operator()(triton::ast::ZxNode& e);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_TRITONTOZ3AST_H */

