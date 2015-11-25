/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <stdexcept>

#include <ControlFlow.h>
#include <Registers.h>
#include <SMT2Lib.h>


SymbolicExpression *ControlFlow::rip(Inst &inst, __uint nextAddr)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  /*
   * Create the SMT semantic.
   * RIP = nextAddress
   */
  expr = smt2lib::bv(nextAddr, REG_SIZE_BIT);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "Program Counter");
  ap.assignmentSpreadTaintRegImm(se, ID_TMP_RIP);

  return se;
}

#endif /* LIGHT_VERSION */

