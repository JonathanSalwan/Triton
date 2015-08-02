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
    uint64 value;

  public:
    ImmediateOperand();
    ImmediateOperand(uint64 value);
    ~ImmediateOperand();

    uint64  getValue(void) const;
    void    setValue(uint64 v);
    void    operator=(const ImmediateOperand &other);
};

#endif     /* !IMMEDIATEOPERAND_H */

