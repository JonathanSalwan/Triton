/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#include <stdexcept>

#include <EflagsBuilder.h>
#include <Registers.h>
#include <SMT2Lib.h>


SymbolicExpression *EflagsBuilder::af(Inst &inst,
                                   SymbolicExpression *parent,
                                   MemRegInterface &dstOp,
                                   smt2lib::smtAstAbstractNode *op1,
                                   smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::af(parent, bvSize, high, low, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_AF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::afNeg(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::afNeg(parent, bvSize, high, low, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_AF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfAdd(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 low  = dstOp.getAbstractLow();
  uint32 high = dstOp.getAbstractHigh();

  expr = EflagsExpressions::cfAdd(parent, high, low, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfImul(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *mulRes)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::cfImul(parent, bvSize, high, low, mulRes);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfMul(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *up)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::cfMul(bvSize, up);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfNeg(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::cfNeg(bvSize, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfRcl(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 high = dstOp.getAbstractHigh();

  expr = EflagsExpressions::cfRcl(parent, high, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfRol(Inst &inst,
                                      SymbolicExpression *parent,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  expr = EflagsExpressions::cfRol(parent, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfRor(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::cfRor(parent, bvSize, high, low, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfSar(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::cfSar(parent, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::cfShl(parent, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfShr(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::cfShr(parent, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfSub(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 low  = dstOp.getAbstractLow();
  uint32 high = dstOp.getAbstractHigh();

  expr = EflagsExpressions::cfSub(parent, high, low, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::clearFlag(Inst &inst,
                                          RegisterOperand &flag)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  expr = EflagsExpressions::clearFlag();

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, flag);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicExpression *EflagsBuilder::clearFlag(Inst &inst,
                                          RegisterOperand &flag,
                                          std::string comment)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  expr = EflagsExpressions::clearFlag();

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, flag, comment);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicExpression *EflagsBuilder::ofAdd(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 low  = dstOp.getAbstractLow();
  uint32 high = dstOp.getAbstractHigh();

  expr = EflagsExpressions::ofAdd(parent, high, low, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofImul(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *mulRes)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::ofImul(parent, bvSize, high, low, mulRes);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofMul(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *up)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::ofMul(bvSize, up);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofNeg(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::ofNeg(parent, bvSize, high, low, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofRol(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::ofRol(parent, bvSize, high, low, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofRor(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();


  expr = EflagsExpressions::ofRor(parent, bvSize, high, low, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofSar(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::ofSar(parent, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();

  expr = EflagsExpressions::ofShl(parent, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofShr(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::ofShr(parent, bvSize, high, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofSub(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 low  = dstOp.getAbstractLow();
  uint32 high = dstOp.getAbstractHigh();

  expr = EflagsExpressions::ofSub(parent, high, low, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::pf(Inst &inst,
                                   SymbolicExpression *parent,
                                   MemRegInterface &dstOp)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::pf(parent, bvSize, high, low);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_PF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::pfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::pfShl(parent, bvSize, high, low, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_PF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::setFlag(Inst &inst,
                                        RegisterOperand &flag)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  expr = EflagsExpressions::setFlag();

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, flag);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicExpression *EflagsBuilder::setFlag(Inst &inst,
                                        RegisterOperand &flag,
                                        std::string comment)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  expr = EflagsExpressions::setFlag();

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, flag, comment);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicExpression *EflagsBuilder::sf(Inst &inst,
                                   SymbolicExpression *parent,
                                   MemRegInterface &dstOp)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 high = dstOp.getAbstractHigh();

  expr = EflagsExpressions::sf(parent, high);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_SF, "Sign flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_SF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::sfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::sfShl(parent, bvSize, high, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_SF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(se, ID_TMP_SF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::zf(Inst &inst,
                                   SymbolicExpression *parent,
                                   MemRegInterface &dstOp)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::zf(parent, bvSize, high, low);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_ZF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::zfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      MemRegInterface &dstOp,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = dstOp.getBitSize();
  uint32 low    = dstOp.getAbstractLow();
  uint32 high   = dstOp.getAbstractHigh();

  expr = EflagsExpressions::zfShl(parent, bvSize, high, low, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_ZF, parent->isTainted);

  return se;
}

#endif /* LIGHT_VERSION */

