//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_CORE_UTIL_H
#define TRITON_CORE_UTIL_H

#include <sstream>
#include <string>
#include <type_traits>

#include <triton/config.hpp>
#include <triton/dllexport.hpp>
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

    //! Converts an object to a string.
    template<typename T>
    inline std::string toString(const T& obj) {
      std::stringstream ss;
      ss << obj;
      return ss.str();
    }

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 10 allocated bytes.
    TRITON_EXPORT void fromUintToBuffer(triton::uint80 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 16 allocated bytes.
    TRITON_EXPORT void fromUintToBuffer(triton::uint128 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 32 allocated bytes.
    TRITON_EXPORT void fromUintToBuffer(triton::uint256 value, triton::uint8* buffer);

    //! Inject the value into the buffer. Make sure that the `buffer` contains at least 64 allocated bytes.
    TRITON_EXPORT void fromUintToBuffer(triton::uint512 value, triton::uint8* buffer);

    //! Casts an triton::uint512 to T
    template <typename T>
    constexpr T cast(const triton::uint512& value) {
      return static_cast<T>(value);
    }

    //! Casts an triton::uint80 to T
    template <typename T>
    constexpr T cast(const triton::uint80& value) {
      return static_cast<T>(value);
    }

    //! Returns the value located into the buffer.
    template <typename T> T cast(const triton::uint8* buffer) {
      // We want to always trigger the static assert when this function is defined (use with a type without specialization)
      // so we have to set the value to false with dependency on T type.
      static_assert(not std::is_same<T, T>::value, "cast have no implementation for this type");
      return {};
    }

    template <> TRITON_EXPORT triton::uint80  cast(const triton::uint8* buffer);
    template <> TRITON_EXPORT triton::uint128 cast(const triton::uint8* buffer);
    template <> TRITON_EXPORT triton::uint256 cast(const triton::uint8* buffer);
    template <> TRITON_EXPORT triton::uint512 cast(const triton::uint8* buffer);

    template <> TRITON_EXPORT triton::uint80  cast(const triton::uint512& value);
    template <> TRITON_EXPORT triton::uint512 cast(const triton::uint80&  value);

  /*! @} End of utils namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CORE_UTIL_H */
