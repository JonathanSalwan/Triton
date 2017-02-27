//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_Z3RESULT_H
#define TRITON_Z3RESULT_H

#include <z3++.h>
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
        virtual ~Z3Result();

        //! Displays the expression.
        void printExpr(void) const;

        //! Sets the expression.
        void setExpr(z3::expr& expr);

        //! Returns the context.
        z3::context& getContext(void);

        //! Returns the expression.
        z3::expr& getExpr(void);

        //! Returns the size of the expression.
        triton::uint32 getBitvectorSize(void);

        //! Returns the value as string.
        std::string getStringValue(void) const;

        //! Returns the value as integer.
        triton::__uint getUintValue(void) const;
    };

  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_Z3RESULT_H */
