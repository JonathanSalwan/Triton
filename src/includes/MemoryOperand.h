/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   MEMORYOPERAND
#define   MEMORYOPERAND

#include <string>

#include "BitsVector.h"
#include "TritonTypes.h"


class MemoryOperand : public BitsVector
{
  private:
    reg_size  address;
    reg_size  size;
    void    copy(const MemoryOperand& other);

  public:
    MemoryOperand();
    MemoryOperand(reg_size address, reg_size size);
    MemoryOperand(const MemoryOperand& other);
    ~MemoryOperand();

    reg_size  getAddress(void) const;
    reg_size  getSize(void) const;
    void    setAddress(reg_size addr);
    void    setSize(reg_size size);
    void    operator=(const MemoryOperand& other);
};

#endif     /* !MEMORYOPERAND */

