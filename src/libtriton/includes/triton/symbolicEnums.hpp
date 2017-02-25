//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICENUMS_H
#define TRITON_SYMBOLICENUMS_H

#include <triton/tritonTypes.hpp>

/*! Defines the name of a symbolic variable. */
#define TRITON_SYMVAR_NAME "SymVar_"

/*! Defines the size of a symbolic variable' name. */
#define TRITON_SYMVAR_NAME_SIZE (sizeof(TRITON_SYMVAR_NAME) - 1)



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

      //! Defines an UNSET symbolic expression.
      const triton::usize UNSET = static_cast<triton::usize>(-1);

      //! Enumerates all kinds of symbolic variable.
      enum symkind_e {
        UNDEF = 0, //!< Undefined
        REG,       //!< Assigned to a register.
        MEM        //!< Assigned to a memory.
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENUMS_H */

