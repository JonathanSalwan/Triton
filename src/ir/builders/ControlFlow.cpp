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


void ControlFlow::rip(Inst &inst, __uint nextAddr)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  /* Don't perform the symbolic execution if the engine is disabled. */
  if (!ap.isSymEngineEnabled())
    return;

  /*
   * Create the SMT semantic.
   * RIP = nextAddress
   */
  expr = smt2lib::bv(nextAddr, REG_SIZE_BIT);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_TMP_RIP, REG_SIZE, "Program Counter");
  ap.assignmentSpreadTaintRegImm(se, ID_TMP_RIP);
}

#endif /* LIGHT_VERSION */

