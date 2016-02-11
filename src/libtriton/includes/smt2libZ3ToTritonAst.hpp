//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_Z3TOTRITONAST_H
#define TRITON_Z3TOTRITONAST_H

#include <z3++.h>
#include "smt2lib.hpp"
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
        smtAstAbstractNode* visit(z3::expr const& expr);


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
        smtAstAbstractNode* convert(void);
    };

  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3TOTRITONAST_H */
