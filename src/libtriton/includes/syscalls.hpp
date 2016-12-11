//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYSCALLS_H
#define TRITON_SYSCALLS_H

#if defined(__unix__) || defined(__APPLE__)

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



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Operating System namespace
  namespace os {
  /*!
   *  \ingroup triton
   *  \addtogroup os
   *  @{
   */

    //! The Unix namespace
    namespace unix {
    /*!
     *  \ingroup os
     *  \addtogroup unix
     *  @{
     */

      #if defined(__unix__)
      //! The number of syscalls 32
      extern const unsigned int NB_SYSCALL32;
      #endif

      //! The number of syscalls 64
      extern const unsigned int NB_SYSCALL64;

      #if defined(__unix__)
      //! The syscall map 32
      extern const char* syscallmap32[];
      #endif

      //! The syscall map 64
      extern const char* syscallmap64[];

    /*! @} End of unix namespace */
    };
  /*! @} End of os namespace */
  };
/*! @} End of triton namespace */
};

#endif /* __unix__ || __APPLE__ */
#endif /* TRITON_SYSCALLS_H */
