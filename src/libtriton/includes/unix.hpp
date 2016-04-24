//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_UNIX_HPP
#define TRITON_UNIX_HPP

#if defined(__unix__) || defined(__APPLE__)

#include <syscalls.hpp>



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Operating System namespace
  namespace os {
  /*!
   *  \ingroup triton
   *  \addtogroup os
   *  @{
   */

    //! \module The Unix namespace
    namespace unix {
    /*!
     *  \ingroup os
     *  \addtogroup unix
     *  @{
     */

      #if defined(__unix__)
      //! Returns the syscall 32 name from its number.
      const char *syscall32NumberToString(__uint syscallNumber);
      #endif

      //! Returns the syscall name from its number.
      const char *syscall64NumberToString(__uint syscallNumber);

    /*! @} End of unix namespace */
    };
  /*! @} End of os namespace */
  };
/*! @} End of triton namespace */
};

#endif /* __unix__ || __APPLE__ */
#endif /* !TRITON_UNIX_HPP */
