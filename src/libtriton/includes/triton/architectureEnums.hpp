//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARCHITECTURE_ENUMS_H
#define TRITON_ARCHITECTURE_ENUMS_H



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
      ARCH_INVALID = 0, /*!< invalid architecture. */
      ARCH_X86,         /*!< x86 architecture. */
      ARCH_X86_64,      /*!< x86_64 architecture. */
      ARCH_LAST_ITEM    /*!< must be the last item.  */
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* ARCHITECTUREENUMS_HPP */
