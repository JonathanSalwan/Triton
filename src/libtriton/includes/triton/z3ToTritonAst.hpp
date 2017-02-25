//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_Z3TOTRITONAST_H
#define TRITON_Z3TOTRITONAST_H

#include <z3++.h>

#include <triton/ast.hpp>
#include <triton/symbolicEngine.hpp>
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

    //! \class Z3ToTritonAst
    /*! \brief Converts a Z3's AST to a Triton's AST. */
    class Z3ToTritonAst {
      private:
        //! Symbolic Engine API
        triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        //! Vists and converts
        triton::ast::AbstractNode* visit(z3::expr const& expr);

      protected:
        //! Z3's context
        z3::context context;

        //! The Z3's expression which must be converted to a Triton's expression.
        z3::expr expr;

      public:
        //! Constructor.
        Z3ToTritonAst(triton::engines::symbolic::SymbolicEngine* symbolicEngine);

        //! Constructor.
        Z3ToTritonAst(triton::engines::symbolic::SymbolicEngine* symbolicEngine, z3::expr& expr);

        //! Constructor by copy.
        Z3ToTritonAst(const Z3ToTritonAst& copy);

        //! Destructor.
        virtual ~Z3ToTritonAst();

        //! Sets the expression.
        void setExpr(z3::expr& expr);

        //! Converts to Triton's AST
        triton::ast::AbstractNode* convert(void);
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3TOTRITONAST_H */
