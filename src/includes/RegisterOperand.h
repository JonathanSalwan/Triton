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
    std::string name;
    uint64      pinRegId;
    uint64      size;
    uint64      tritonRegId;
    void        copy(const RegisterOperand& other);

  public:
    RegisterOperand();
    RegisterOperand(uint64 pinRegId);
    RegisterOperand(const RegisterOperand& other);
    ~RegisterOperand();

    std::string getName(void) const;
    uint64      getPinRegId(void) const;
    uint64      getSize(void) const;
    uint64      getTritonRegId(void) const;
    void        setSize(uint64 size);
    void        setTritonRegId(uint64 tritonRegId);
    void        operator=(const RegisterOperand& other);
};

#endif     /* !REGISTEROPERAND_H */

