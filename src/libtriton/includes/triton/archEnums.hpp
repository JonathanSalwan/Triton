//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARCHENUMS_H
#define TRITON_ARCHENUMS_H


//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! The architectures */
    enum architectures_e {
      ARCH_INVALID = 0, /*!< Invalid architecture.   */
      ARCH_X86,         /*!< X86 architecture.       */
      ARCH_X86_64,      /*!< X86_64 architecture.    */
      ARCH_AArch64,     /*!< AArch64 architecture.   */
      ARCH_LAST_ITEM    /*!< Must be the last item.  */
    };

    /*! Endianness */
    enum endianness_e {
      INVALID_ENDIANNESS = 0,   /*!< Invalid endianness */
      LE,                       /*!< Little endian.     */
      BE,                       /*!< Big endian.        */
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARCHENUMS_HPP */
