//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef __unix__

#include <syscalls.hpp>
#include <tritonTypes.hpp>
#include <unix.hpp>



namespace triton {
  namespace os {
    namespace unix {

      const char *syscall32NumberToString(triton::uint32 syscallNumber) {
        if (syscallNumber >= 0 && syscallNumber < (triton::uint32) NB_SYSCALL32)
          return syscallmap32[syscallNumber];
        else
          return nullptr;
      }

      const char *syscall64NumberToString(triton::uint32 syscallNumber) {
        if (syscallNumber >= 0 && syscallNumber < (triton::uint32) NB_SYSCALL64)
          return syscallmap64[syscallNumber];
        else
          return nullptr;
      }

    }; /* unix namespace */
  }; /* os namespace */
}; /* triton namespace */

#endif /* __unix__ */
