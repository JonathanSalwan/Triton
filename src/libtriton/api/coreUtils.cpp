//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <coreUtils.hpp>
#include <cpuSize.hpp>



/*
** Note: As the triton::uint128 is different between x86 and x86_64,
**       we must use generic methods to deal with big int.
*/

namespace triton {

  void fromUint128ToBuffer(triton::uint128 value, triton::uint8* buffer) {
    for (triton::uint32 i = 0; i < DQWORD_SIZE; i++) {
      buffer[i] = static_cast<triton::uint8>(value & 0xff);
      value >>= BYTE_SIZE_BIT;
    }
  }


  triton::uint128 fromBufferToUint128(triton::uint8* buffer) {
    triton::uint128 value = 0;
    for (triton::sint32 i = DQWORD_SIZE-1; i >= 0; i--)
      value = ((value << BYTE_SIZE_BIT) | buffer[i]);
    return value;
  }

}; /* triton namespace */

