//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYSCALLS_H
#define TRITON_SYSCALLS_H

#ifdef __unix__

  #ifdef __APPLE__
    #include <sys/syscall.h>
  #else
    #if defined(__x86_64__) || defined(_M_X64)
      #include <asm/unistd_64.h>
    #endif
    #if defined(__i386) || defined(_M_IX86)
      #include <asm/unistd_32.h>
    #endif
  #endif



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

      //! The number of syscalls 32
      extern const unsigned int NB_SYSCALL32;

      //! The number of syscalls 64
      extern const unsigned int NB_SYSCALL64;

      //! The syscall map 32
      extern const char *syscallmap32[];

      //! The syscall map 64
      extern const char *syscallmap64[];

    /*! @} End of unix namespace */
    };
  /*! @} End of os namespace */
  };
/*! @} End of triton namespace */
};

#endif /* __unix__ */
#endif /* TRITON_SYSCALLS_H */
