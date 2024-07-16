//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_EXTERNALLIBS_HPP
#define TRITON_EXTERNALLIBS_HPP



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */
  //! The external libraries namespace
  namespace extlibs {
  /*!
   *  \addtogroup triton
   *  @{
   */

    //! The Capstone library namespace
    namespace capstone {
    /*!
     *  \addtogroup extlibs
     *  @{
     */
      #include <capstone/arm.h>
      #include <capstone/arm64.h>
      #include <capstone/capstone.h>
      #ifdef COMPILE_RISCV
      #include <capstone/riscv.h>
      #endif
      #include <capstone/x86.h>
    /*! @} End of capstone namespace */
    };

  /*! @} End of extlibs namespace */
  };
/*! @} End of triton namespace */
};

#endif  /* TRITON_EXTERNALLIBS_HPP */
