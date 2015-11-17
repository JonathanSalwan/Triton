/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <iostream>

#include <Syscalls.h>
#include <TritonTypes.h>


extern const char *syscallmap[];

const char *syscallNumberLinux64ToString(reg_size syscallNumber) {
  if (syscallNumber >= 0 && syscallNumber < (reg_size) NB_SYSCALL)
    return syscallmap[syscallNumber];
  else
    return nullptr;
}
