/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   MEMORYOPERAND
#define   MEMORYOPERAND

#include <string>

#include "BitsVector.h"
#include "CpuSize.h"
#include "MemRegInterface.h"
#include "TritonTypes.h"


class MemoryOperand : public BitsVector, public MemRegInterface
{
  private:
    __uint  address;
    __uint  size;
    void    copy(const MemoryOperand& other);

  public:
    MemoryOperand();
    MemoryOperand(__uint address, __uint size);
    MemoryOperand(const MemoryOperand& other);
    ~MemoryOperand();

    __uint          getAbstractHigh(void) const;
    __uint          getAbstractLow(void) const;
    __uint          getAddress(void) const;
    __uint          getBitSize(void) const;
    __uint          getSize(void) const;
    void            operator=(const MemoryOperand& other);
    void            setAddress(__uint addr);
    void            setSize(__uint size);
};

#endif     /* !MEMORYOPERAND */

