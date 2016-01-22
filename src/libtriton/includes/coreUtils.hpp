//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_CORE_UTIL_H
#define TRITON_CORE_UTIL_H

#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! Inject the value into the buffer.
  void fromUint128ToBuffer(triton::uint128 value, triton::uint8* buffer);

  //! Returns the value located into the buffer.
  triton::uint128 fromBufferToUint128(triton::uint8* buffer);

/*! @} End of triton namespace */
};

#endif /* TRITON_CORE_UTIL_H */

