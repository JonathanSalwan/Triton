/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYSCALLS_H
#define TRITON_SYSCALLS_H

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

extern const unsigned int NB_SYSCALL;
extern const char *syscallmap[];

#endif // SYSCALLS_H
