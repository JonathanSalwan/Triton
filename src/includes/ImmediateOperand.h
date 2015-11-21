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
    __uint  value;
    void    copy(const ImmediateOperand& other);

  public:
    ImmediateOperand();
    ImmediateOperand(__uint value);
    ImmediateOperand(const ImmediateOperand& other);
    ~ImmediateOperand();

    __uint  getValue(void) const;
    void    setValue(__uint v);
    void    operator=(const ImmediateOperand& other);
};

#endif     /* !IMMEDIATEOPERAND_H */

