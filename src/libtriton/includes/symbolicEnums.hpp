//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICENUMS_H
#define TRITON_SYMBOLICENUMS_H

#include "tritonTypes.hpp"

/*! Defines the name of a symbolic variable. */
#define TRITON_SYMVAR_NAME "SymVar_"

/*! Defines the size of a symbolic variable' name. */
#define TRITON_SYMVAR_NAME_SIZE (sizeof(TRITON_SYMVAR_NAME) - 1)



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      //! Defines an UNSET symbolic expression.
      const triton::__uint UNSET = -1;

      //! Enumerates all kinds of symbolic variable.
      enum symkind_e {
        UNDEF = 0, //!< Undefined
        REG,       //!< Assigned to a register.
        MEM        //!< Assigned to a memory.
      };

      //! Enumerates all Kinds of symbolic optimization.
      enum optimization_e {
        ALIGNED_MEMORY,        //!< Keep a map of aligned memory.
        AST_DICTIONARIES,      //!< Abstract Syntax Tree dictionaries.
        ONLY_ON_SYMBOLIZED,    //!< Perform symbolic execution only on symbolized expressions.
        ONLY_ON_TAINTED,       //!< Perform symbolic execution only on tainted instructions.
        PC_TRACKING_SYMBOLIC,  //!< Track path constraints only if they are symbolized.
      };

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICENUMS_H */

