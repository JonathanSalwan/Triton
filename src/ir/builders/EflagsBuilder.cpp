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
                                   AnalysisProcessor &ap,
                                   uint32 dstSize,
                                   smt2lib::smtAstAbstractNode *op1,
                                   smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::af(parent, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_AF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::afNeg(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::afNeg(parent, bvSize, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_AF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfAdd(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfAdd(parent, bvSize, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfImul(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *mulRes)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfImul(parent, bvSize, mulRes);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfMul(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *up)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfMul(bvSize, up);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfNeg(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfNeg(bvSize, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfRcl(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfRcl(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfRol(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;

  expr = EflagsExpressions::cfRol(parent, ap, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfRor(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfRor(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfSar(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfSar(parent, ap, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfShl(parent, ap, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfShr(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfShr(parent, ap, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::cfSub(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::cfSub(parent, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_CF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::clearFlag(Inst &inst,
                                          AnalysisProcessor &ap,
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
                                          AnalysisProcessor &ap,
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
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 extractSize = (dstSize * REG_SIZE) - 1;

  expr = EflagsExpressions::ofAdd(parent, extractSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofImul(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *mulRes)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofImul(parent, bvSize, mulRes);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofMul(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *up)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofMul(bvSize, up);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofNeg(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofNeg(parent, bvSize, op1);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofRol(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofRol(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofRor(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofRor(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofSar(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofSar(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofShl(parent, ap, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofShr(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::ofShr(parent, ap, bvSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::ofSub(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op1,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 extractSize = (dstSize * REG_SIZE) - 1;

  expr = EflagsExpressions::ofSub(parent, extractSize, op1, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_OF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::pf(Inst &inst,
                                   SymbolicExpression *parent,
                                   AnalysisProcessor &ap,
                                   uint32 dstSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::pf(parent, bvSize);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_PF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::pfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::pfShl(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_PF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::setFlag(Inst &inst,
                                        AnalysisProcessor &ap,
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
                                        AnalysisProcessor &ap,
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
                                   AnalysisProcessor &ap,
                                   uint32 dstSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 extractSize = (dstSize * REG_SIZE) - 1;

  expr = EflagsExpressions::sf(parent, extractSize);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_SF, "Sign flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_SF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::sfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);
  uint32 extractSize = (dstSize * REG_SIZE) - 1;

  expr = EflagsExpressions::sfShl(parent, ap, bvSize, extractSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_SF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(se, ID_TMP_SF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::zf(Inst &inst,
                                   SymbolicExpression *parent,
                                   AnalysisProcessor &ap,
                                   uint32 dstSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::zf(parent, bvSize);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_ZF, parent->isTainted);

  return se;
}


SymbolicExpression *EflagsBuilder::zfShl(Inst &inst,
                                      SymbolicExpression *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      smt2lib::smtAstAbstractNode *op2)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *expr;
  uint32 bvSize = (dstSize * REG_SIZE);

  expr = EflagsExpressions::zfShl(parent, ap, bvSize, op2);

  /* Create the symbolic expression */
  se = ap.createFlagSE(inst, expr, ID_TMP_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_TMP_ZF, parent->isTainted);

  return se;
}

#endif /* LIGHT_VERSION */

