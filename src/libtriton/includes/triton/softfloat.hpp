//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_SOFTFLOAT_HPP
#define TRITON_SOFTFLOAT_HPP

#include <cstdint>

//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */
    //! The Softfloat namespace
    namespace sf {
    /*!
     *  \ingroup triton
     *  \addtogroup softfloat
     *  @{
     */

    //! Cast 32-bit floating point value to 16-bit according to IEEE-754
    auto f32_to_f16(float value) -> uint16_t;

  /*! @} End of softfloat namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SOFTFLOAT_HPP */
