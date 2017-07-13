//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PIN_API_H
#define TRITON_PIN_API_H

#include <triton/api.hpp>



//! The Tracer namespace
namespace tracer {
/*!
 *  \addtogroup tracer
 *  @{
 */

  //! The Pintool namespace
  namespace pintool {
  /*!
   *  \ingroup tracer
   *  \addtogroup pintool
   *  @{
   */

    //! The triton api for the pintool.
    extern triton::API api;

  /*! @} End of pintool namespace */
  };
/*! @} End of tracer namespace */
};

#endif
