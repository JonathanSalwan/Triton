/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   IMMEDIATEOPERAND_H
#define   IMMEDIATEOPERAND_H

#include <string>

#include "TritonTypes.h"


class ImmediateOperand
{
  private:
    reg_size  value;
    void    copy(const ImmediateOperand& other);

  public:
    ImmediateOperand();
    ImmediateOperand(reg_size value);
    ImmediateOperand(const ImmediateOperand& other);
    ~ImmediateOperand();

    reg_size  getValue(void) const;
    void    setValue(reg_size v);
    void    operator=(const ImmediateOperand& other);
};

#endif     /* !IMMEDIATEOPERAND_H */

