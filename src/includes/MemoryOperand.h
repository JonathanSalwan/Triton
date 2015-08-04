/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   MEMORYOPERAND
#define   MEMORYOPERAND

#include <string>

#include "TritonTypes.h"


class MemoryOperand
{
  private:
    uint64  address;
    uint64  size;
    void    copy(const MemoryOperand& other);

  public:
    MemoryOperand();
    MemoryOperand(uint64 address, uint64 size);
    MemoryOperand(const MemoryOperand& other);
    ~MemoryOperand();

    uint64  getAddress(void) const;
    uint64  getSize(void) const;
    void    setAddress(uint64 addr);
    void    setSize(uint64 size);
    void    operator=(const MemoryOperand& other);
};

#endif     /* !MEMORYOPERAND */

