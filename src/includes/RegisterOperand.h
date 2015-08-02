/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   REGISTEROPERAND_H
#define   REGISTEROPERAND_H

#include <string>

#include "BitsVector.h"
#include "TritonTypes.h"


class RegisterOperand : public BitsVector
{
  private:
    uint64 tritonRegId;
    uint64 pinRegId;
    uint64 size;

  public:
    RegisterOperand();
    RegisterOperand(uint64 pinRegId);
    ~RegisterOperand();

    uint64 getTritonRegId(void) const;
    uint64 getPinRegId(void) const;
    uint64 getSize(void) const;
    void   setSize(uint64 size);
    void   operator=(const RegisterOperand &other);
};

#endif     /* !REGISTEROPERAND_H */

