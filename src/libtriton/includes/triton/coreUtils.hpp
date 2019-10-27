//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CORE_UTIL_H
#define TRITON_CORE_UTIL_H

#include <triton/triton_export.h>
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
    TRITON_EXPORT void fromUintToBuffer(triton::uint128 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 32 allocated bytes.
    TRITON_EXPORT void fromUintToBuffer(triton::uint256 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 64 allocated bytes.
    TRITON_EXPORT void fromUintToBuffer(triton::uint512 value, triton::uint8* buffer);

    //! Returns the value located into the buffer.
    template <typename T> TRITON_EXPORT T fromBufferToUint(const triton::uint8* buffer) {
      // We want to always trigger the static assert when this function is defined (use with a type without specialization)
      // so we have to set the value to false with dependency on T type.
      static_assert(not std::is_same<T, T>::value, "fromBufferToUint have no implementation for this type");
      return {};
    }

    template <> TRITON_EXPORT triton::uint128 fromBufferToUint(const triton::uint8* buffer);
    template <> TRITON_EXPORT triton::uint256 fromBufferToUint(const triton::uint8* buffer);
    template <> TRITON_EXPORT triton::uint512 fromBufferToUint(const triton::uint8* buffer);

  /*! @} End of triton namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CORE_UTIL_H */
