//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_CPUSIZE_H
#define TRITON_CPUSIZE_H

#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Size namespace
  namespace size {
  /*!
   *  \ingroup triton
   *  \addtogroup size
   *  @{
   */
    //! byte size in byte
    constexpr triton::uint32 byte          = 1;
    //! word size in byte
    constexpr triton::uint32 word          = 2;
    //! dword size in byte
    constexpr triton::uint32 dword         = 4;
    //! qword size in byte
    constexpr triton::uint32 qword         = 8;
    //! fword size in byte
    constexpr triton::uint32 fword         = 10;
    //! dqword size in byte
    constexpr triton::uint32 dqword        = 16;
    //! qqword size in byte
    constexpr triton::uint32 qqword        = 32;
    //! dqqword size in byte
    constexpr triton::uint32 dqqword       = 64;
    //! max size supported in byte
    constexpr triton::uint32 max_supported = dqqword;
  /*! @} End of size namespace */
  };

  //! The BitSize namespace
  namespace bitsize {
  /*!
   *  \ingroup triton
   *  \addtogroup bitsize
   *  @{
   */
    //! flag size in bit
    constexpr triton::uint32 flag          = 1;
    //! byte size in bit
    constexpr triton::uint32 byte          = 8;
    //! word size in bit
    constexpr triton::uint32 word          = 16;
    //! dword size in bit
    constexpr triton::uint32 dword         = 32;
    //! qword size in bit
    constexpr triton::uint32 qword         = 64;
    //! fword size in bit
    constexpr triton::uint32 fword         = 80;
    //! dqword size in bit
    constexpr triton::uint32 dqword        = 128;
    //! qqword size in bit
    constexpr triton::uint32 qqword        = 256;
    //! dqqword size in bit
    constexpr triton::uint32 dqqword       = 512;
    //! max size supported in bit
    constexpr triton::uint32 max_supported = dqqword;
  /*! @} End of bitsize namespace */
  };

/*! @} End of triton namespace */
};

#endif /* TRITON_CPUSIZE_H */
