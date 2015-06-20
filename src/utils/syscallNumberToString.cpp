
#include <iostream>
#include <Syscalls.h>


extern const char *syscallmap[];

const char *syscallNumberLinux64ToString(uint64_t syscallNumber)
{
  if (syscallNumber > 0 && syscallNumber < (uint64_t) NB_SYSCALL)
    return syscallmap[syscallNumber];
  else
    return nullptr;
}
