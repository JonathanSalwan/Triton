//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_STUBS_HPP
#define TRITON_STUBS_HPP

#include <map>
#include <vector>

#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Stubs namespace
  namespace stubs {
  /*!
   *  \ingroup triton
   *  \addtogroup stubs
   *  @{
   */

    //! The systemv namespace
    namespace systemv {
    /*!
     *  \ingroup stubs
     *  \addtogroup systemv
     *  @{
     */

      //! The linux namespace
      namespace libc {
      /*!
       *  \ingroup systemv
       *  \addtogroup libc
       *  @{
       */

        /*! Symbols mapping. Each entry points on its position in `systemv::libc::code`. Example: strcmp -> 0x601. */
        extern std::map<std::string, triton::uint64> symbols;

        /*! Position independent code of some libc functions */
        extern std::vector<triton::uint8> code;

      /*! @} End of libc namespace */
      };
    /*! @} End of systemv namespace */
    };
  /*! @} End of stubs namespace */
  };
/*! @} End of triton namespace */
}; /* triton namespace */

#endif /* TRITON_STUBS_HPP */
