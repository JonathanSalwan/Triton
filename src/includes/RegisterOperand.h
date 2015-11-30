/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   REGISTEROPERAND_H
#define   REGISTEROPERAND_H

#include <string>

#include "BitsVector.h"
#include "CpuSize.h"
#include "MemRegInterface.h"
#include "TritonTypes.h"


class RegisterOperand : public BitsVector, public MemRegInterface
{
  private:
    std::string name;
    __uint      pinRegId;
    __uint      size;
    __uint      tritonRegId;
    void        copy(const RegisterOperand& other);

  public:
    RegisterOperand();
    RegisterOperand(__uint pinRegId, __uint size=0);
    RegisterOperand(const RegisterOperand& other);
    ~RegisterOperand();

    bool            isValid(void);
    std::string     getName(void) const;
    __uint          getAbstractHigh(void) const;
    __uint          getAbstractLow(void) const;
    __uint          getBitSize(void) const;
    __uint          getPinRegId(void) const;
    __uint          getSize(void) const;
    __uint          getTritonRegId(void) const;
    void            setSize(__uint size);
    void            setTritonRegId(__uint tritonRegId);
    void            operator=(const RegisterOperand& other);

};

#endif     /* !REGISTEROPERAND_H */

