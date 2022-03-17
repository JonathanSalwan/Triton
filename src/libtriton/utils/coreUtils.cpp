//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>



namespace triton {
  namespace utils {

    void fromUintToBuffer(triton::uint80 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::fword; i++) {
        buffer[i] = static_cast<triton::uint8>(value & 0xff);
        value >>= triton::bitsize::byte;
      }
    }


    void fromUintToBuffer(triton::uint128 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::dqword; i++) {
        buffer[i] = static_cast<triton::uint8>(value & 0xff);
        value >>= triton::bitsize::byte;
      }
    }


    void fromUintToBuffer(triton::uint256 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::qqword; i++) {
        buffer[i] = static_cast<triton::uint8>(value & 0xff);
        value >>= triton::bitsize::byte;
      }
    }


    void fromUintToBuffer(triton::uint512 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::dqqword; i++) {
        buffer[i] = static_cast<triton::uint8>(value & 0xff);
        value >>= triton::bitsize::byte;
      }
    }


    template <> triton::uint80 cast<>(const triton::uint8* buffer) {
      triton::uint80 value = 0;
      for (triton::sint32 i = triton::size::fword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    template <> triton::uint128 cast<>(const triton::uint8* buffer) {
      triton::uint128 value = 0;
      for (triton::sint32 i = triton::size::dqword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    template <> triton::uint256 cast<>(const triton::uint8* buffer) {
      triton::uint256 value = 0;
      for (triton::sint32 i = triton::size::qqword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    template <> triton::uint512 cast<>(const triton::uint8* buffer) {
      triton::uint512 value = 0;
      for (triton::sint32 i = triton::size::dqqword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    //! Cast an uint512 to an uint80 according to the multiprecision library
    template <> triton::uint80 cast<>(const triton::uint512& value) {
      #ifdef TRITON_BOOST_INTERFACE
        return static_cast<triton::uint80>(value);
      #else
        #if defined(WIDE_INTEGER_NAMESPACE)
        using WIDE_INTEGER_NAMESPACE::math::wide_integer::detail::make_lo;
        using WIDE_INTEGER_NAMESPACE::math::wide_integer::detail::make_hi;
        #else
        using math::wide_integer::detail::make_lo;
        using math::wide_integer::detail::make_hi;
        #endif

        static_assert(
          std::numeric_limits<typename triton::uint80::limb_type>::digits * 2 == std::numeric_limits<typename triton::uint512::limb_type>::digits,
          "Error: Wrong input/output limb types for this conversion"
        );

        using local_value_type = typename triton::uint80::representation_type::value_type;

        return triton::uint80::from_rep({
                 make_lo<local_value_type>(*(value.crepresentation().data() + 0U)),
                 make_hi<local_value_type>(*(value.crepresentation().data() + 0U)),
                 make_lo<local_value_type>(*(value.crepresentation().data() + 1U)),
                 make_hi<local_value_type>(*(value.crepresentation().data() + 1U)),
                 make_lo<local_value_type>(*(value.crepresentation().data() + 2U))
               });
      #endif
    }


    //! Cast an uint80 to an uint512 according to the multiprecision library
    template <> triton::uint512 cast<>(const triton::uint80& value) {
      #ifdef TRITON_BOOST_INTERFACE
        return static_cast<triton::uint512>(value);
      #else
        #if defined(WIDE_INTEGER_NAMESPACE)
        using WIDE_INTEGER_NAMESPACE::math::wide_integer::detail::make_large;
        #else
        using math::wide_integer::detail::make_large;
        #endif

        static_assert(
          std::numeric_limits<typename triton::uint80::limb_type>::digits * 2 == std::numeric_limits<typename triton::uint512::limb_type>::digits,
          "Error: Wrong input/output limb types for this conversion"
        );

        using local_value_type = typename triton::uint80::representation_type::value_type;

        return triton::uint512::from_rep({
                 make_large(*(value.crepresentation().data() + 0U), *(value.crepresentation().data() + 1U)),
                 make_large(*(value.crepresentation().data() + 2U), *(value.crepresentation().data() + 3U)),
                 make_large(*(value.crepresentation().data() + 4U), static_cast<local_value_type>(0U))
               });
      #endif
    }

  }; /* utils namespace */
}; /* triton namespace */
