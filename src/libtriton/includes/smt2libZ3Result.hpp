//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_Z3RESULT_H
#define TRITON_Z3RESULT_H

#include <z3++.h>
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

    //! \class Z3Result
    /*! \brief The result class. */
    class Z3Result {
      protected:
        //! The context.
        z3::context context;

        //! The expression.
        z3::expr expr;

      public:

        //! Constructor.
        Z3Result();

        //! Constructor by copy.
        Z3Result(const Z3Result& copy);

        //! Destructor.
        ~Z3Result();

        //! Displays the expression.
        void printExpr(void) const;

        //! Sets the expression.
        void setExpr(z3::expr& expr);

        //! Returns the context.
        z3::context& getContext(void);

        //! Returns the expression.
        z3::expr& getExpr(void);

        //! Returns the expression's size.
        triton::uint32 getBitvectorSize(void);

        //! Returns the value as string.
        std::string getStringValue(void) const;

        //! Returns the value as integer.
        triton::__uint getUintValue(void) const;
    };

  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3RESULT_H */
