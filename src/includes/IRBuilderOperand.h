/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   RBUILDEROPERAND_H
#define   RBUILDEROPERAND_H

// Define each type of operand.
namespace IRBuilderOperand
{
  enum operand_t {UNDEF = 0, IMM, REG, MEM_R, MEM_W, LEA};
};

#endif     /* !__IRBUILDEROPERAND_H__ */
