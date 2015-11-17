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
    reg_size      pinRegId;
    reg_size      size;
    reg_size      tritonRegId;
    void        copy(const RegisterOperand& other);

  public:
    RegisterOperand();
    RegisterOperand(reg_size pinRegId);
    RegisterOperand(const RegisterOperand& other);
    ~RegisterOperand();

    std::string getName(void) const;
    reg_size      getPinRegId(void) const;
    reg_size      getSize(void) const;
    reg_size      getTritonRegId(void) const;
    void        setSize(reg_size size);
    void        setTritonRegId(reg_size tritonRegId);
    void        operator=(const RegisterOperand& other);
};

#endif     /* !REGISTEROPERAND_H */

