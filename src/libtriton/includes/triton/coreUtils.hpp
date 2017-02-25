//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CORE_UTIL_H
#define TRITON_CORE_UTIL_H

#include <triton/tritonTypes.hpp>


//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Utils namespace
  namespace utils {
  /*!
   *  \ingroup triton
   *  \addtogroup utils
   *  @{
   */

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 16 allocated bytes.
    void fromUintToBuffer(triton::uint128 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 32 allocated bytes.
    void fromUintToBuffer(triton::uint256 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 64 allocated bytes.
    void fromUintToBuffer(triton::uint512 value, triton::uint8* buffer);

    //! Returns the value located into the buffer.
    template <typename T> T fromBufferToUint(const triton::uint8* buffer);

  /*! @} End of triton namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CORE_UTIL_H */

