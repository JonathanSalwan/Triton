//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>



/*
 * Note: We must use generic methods to deal with big int and arrays.
 */

namespace triton {
  namespace utils {

    void fromUintToBuffer(triton::uint128 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < DQWORD_SIZE; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= BYTE_SIZE_BIT;
      }
    }


    void fromUintToBuffer(triton::uint256 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < QQWORD_SIZE; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= BYTE_SIZE_BIT;
      }
    }


    void fromUintToBuffer(triton::uint512 value, triton::uint8* buffer) {
      for (triton::uint32 i = 0; i < DQQWORD_SIZE; i++) {
        buffer[i] = (value & 0xff).convert_to<triton::uint8>();
        value >>= BYTE_SIZE_BIT;
      }
    }


    template <> triton::uint128 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint128 value = 0;
      for (triton::sint32 i = DQWORD_SIZE-1; i >= 0; i--)
        value = ((value << BYTE_SIZE_BIT) | buffer[i]);
      return value;
    }


    template <> triton::uint256 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint256 value = 0;
      for (triton::sint32 i = QQWORD_SIZE-1; i >= 0; i--)
        value = ((value << BYTE_SIZE_BIT) | buffer[i]);
      return value;
    }


    template <> triton::uint512 fromBufferToUint<>(const triton::uint8* buffer) {
      triton::uint512 value = 0;
      for (triton::sint32 i = DQQWORD_SIZE-1; i >= 0; i--)
        value = ((value << BYTE_SIZE_BIT) | buffer[i]);
      return value;
    }

  }; /* utils namespace */
}; /* triton namespace */

