//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CALLBACKSENUMS_HPP
#define TRITON_CALLBACKSENUMS_HPP



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Callbacks namespace
  namespace callbacks {
  /*!
   *  \ingroup triton
   *  \addtogroup callbacks
   *  @{
   */

    /*! Enumerates all kinds callbacks. */
    enum callback_e {
      GET_CONCRETE_MEMORY_VALUE,    /*!< LOAD concrete memory value callback */
      GET_CONCRETE_REGISTER_VALUE,  /*!< GET concrete register value callback */
      SET_CONCRETE_MEMORY_VALUE,    /*!< STORE concrete memory value callback */
      SET_CONCRETE_REGISTER_VALUE,  /*!< PUT concrete register value callback */
      SYMBOLIC_SIMPLIFICATION,      /*!< Symbolic simplification callback */
    };

  /*! @} End of callbacks namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CALLBACKSENUMS_HPP */
