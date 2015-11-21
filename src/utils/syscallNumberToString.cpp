/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <iostream>

#include <Syscalls.h>
#include <TritonTypes.h>


extern const char *syscallmap[];

const char *syscallNumberLinuxToString(__uint syscallNumber) {
  if (syscallNumber >= 0 && syscallNumber < (__uint) NB_SYSCALL)
    return syscallmap[syscallNumber];
  else
    return nullptr;
}
