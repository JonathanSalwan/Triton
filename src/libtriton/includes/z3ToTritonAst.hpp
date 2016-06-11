//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_Z3TOTRITONAST_H
#define TRITON_Z3TOTRITONAST_H

#include <z3++.h>
#include "ast.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \class Z3ToTritonAst
    /*! \brief Converts a Z3's AST to a Triton's AST. */
    class Z3ToTritonAst {
      protected:
        //! Z3's context
        z3::context context;

        //! The Z3's expression which must be converted to a Triton's expression.
        z3::expr expr;


      private:
        //! Vists and converts
        triton::ast::AbstractNode* visit(z3::expr const& expr);


      public:
        //! Constructor.
        Z3ToTritonAst();

        //! Constructor.
        Z3ToTritonAst(z3::expr& expr);

        //! Constructor by copy.
        Z3ToTritonAst(const Z3ToTritonAst& copy);

        //! Destructor.
        ~Z3ToTritonAst();

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
