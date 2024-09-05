//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/softfloat.hpp>

#include <cstring>

namespace triton {
  namespace sf {

    auto f32_to_f16(float value) -> uint16_t {
      uint32_t f;
      static_assert(sizeof(float) == sizeof(uint32_t),
                    "Unexpected float type size");
      std::memcpy(&f, &value, sizeof(uint32_t));
      uint16_t sign = (f >> 16) & 0x8000;
      int16_t exponent = ((f >> 23) & 0xff) - 127 + 15;
      uint16_t mantissa = (f >> 13) & 0x3ff;
      if (exponent <= 0) {
        if (exponent < -10) {
          return sign;
        }
        mantissa = (mantissa | 0x400) >> (1 - exponent);
        return sign | mantissa;
      } else if (exponent == 0xff - (127 - 15)) {
        if (mantissa) {
          return sign | 0x7fff;
        } else {
          return sign | 0x7c00;
        }
      } else if (exponent > 30) {
        return sign | 0x7c00;
      }
      return sign | (exponent << 10) | mantissa;
    }

  }  /* sf namespace */
} /* triton namespace */