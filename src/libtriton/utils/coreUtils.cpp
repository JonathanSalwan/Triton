//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>



/*
 * Note: We must use generic methods to deal with big int and arrays.
 */

namespace triton {
  namespace utils {

    void fromUintToBuffer(triton::uint80 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::fword; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= triton::bitsize::byte;
      }
    }


    void fromUintToBuffer(triton::uint128 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::dqword; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= triton::bitsize::byte;
      }
    }


    void fromUintToBuffer(triton::uint256 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::qqword; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= triton::bitsize::byte;
      }
    }


    void fromUintToBuffer(triton::uint512 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < triton::size::dqqword; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= triton::bitsize::byte;
      }
    }


    template <> triton::uint80 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint80 value = 0;
      for (triton::sint32 i = triton::size::fword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    template <> triton::uint128 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint128 value = 0;
      for (triton::sint32 i = triton::size::dqword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    template <> triton::uint256 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint256 value = 0;
      for (triton::sint32 i = triton::size::qqword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }


    template <> triton::uint512 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint512 value = 0;
      for (triton::sint32 i = triton::size::dqqword-1; i >= 0; i--)
        value = ((value << triton::bitsize::byte) | buffer[i]);
      return value;
    }

  }; /* utils namespace */
}; /* triton namespace */
