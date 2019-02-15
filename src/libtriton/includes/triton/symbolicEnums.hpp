//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICENUMS_HPP
#define TRITON_SYMBOLICENUMS_HPP

/*! Defines the default name of a symbolic variable. */
#define TRITON_SYMVAR_NAME "SymVar_"



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! Type of symbolic expressions.
      enum expression_e {
        MEMORY_EXPRESSION,     //!< Assigned to a memory expression.
        REGISTER_EXPRESSION,   //!< Assigned to a register expression.
        VOLATILE_EXPRESSION,   //!< Assigned to a volatile expression.
      };

      //! Type of symbolic variable.
      enum variable_e {
        MEMORY_VARIABLE,       //!< Variable assigned to a memory.
        REGISTER_VARIABLE,     //!< Variable assigned to a register.
        UNDEFINED_VARIABLE,    //!< Undefined assignment.
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENUMS_HPP */
