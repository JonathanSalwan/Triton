/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   REGISTEROPERAND_H
#define   REGISTEROPERAND_H

#include <string>

#include "ExtractBits.h"
#include "TritonTypes.h"


class RegisterOperand
{
  private:
    ExtractBits   bitsVector;
    std::string   name;
    uint64        id;

  public:
    RegisterOperand(uint64 regId);
    ~RegisterOperand();

    const ExtractBits&  getBitsVector(void);
    const std::string&  getName(void);
    uint64              getId(void);
};

#endif     /* !REGISTEROPERAND_H */

