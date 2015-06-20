#include <boost/format.hpp>
#include <stdexcept>

#include <EflagsBuilder.h>
#include <Registers.h>



SymbolicElement *EflagsBuilder::af(Inst &inst,
                                   SymbolicElement *parent,
                                   AnalysisProcessor &ap,
                                   uint32 dstSize,
                                   std::stringstream &op1,
                                   std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::af(parent, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_AF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::afNeg(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::afNeg(parent, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_AF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfAdd(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::cfAdd(parent, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfImul(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::cfImul(parent, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfMul(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &up)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfMul(bvSize, up);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfNeg(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfNeg(bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfRol(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfRol(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfRor(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfRor(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfSar(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfSar(parent, ap, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfShl(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfShl(parent, ap, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfShr(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfShr(parent, ap, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfSub(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::cfSub(op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_CF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::clearFlag(Inst &inst,
                                          AnalysisProcessor &ap,
                                          regID_t flag)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::clearFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, flag);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::clearFlag(Inst &inst,
                                          AnalysisProcessor &ap,
                                          regID_t flag,
                                          std::string comment)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::clearFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, flag, comment);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::ofAdd(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::ofAdd(parent, extractSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofImul(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::ofImul(parent, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofMul(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &up)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofMul(bvSize, up);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofNeg(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofNeg(parent, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofRol(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofRol(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofRor(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofRor(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofSar(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofSar(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofShl(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofShl(parent, ap, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofShr(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofShr(parent, ap, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofSub(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::ofSub(parent, extractSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_OF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::pf(Inst &inst,
                                   SymbolicElement *parent,
                                   AnalysisProcessor &ap)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::pf(parent);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_PF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::pfShl(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::pfShl(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_PF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::setFlag(Inst &inst,
                                        AnalysisProcessor &ap,
                                        regID_t flag)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::setFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, flag);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::setFlag(Inst &inst,
                                        AnalysisProcessor &ap,
                                        regID_t flag,
                                        std::string comment)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::setFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, flag, comment);

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::sf(Inst &inst,
                                   SymbolicElement *parent,
                                   AnalysisProcessor &ap,
                                   uint32 dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::sf(parent, extractSize);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_SF, "Sign flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_SF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::sfShl(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);
  uint32              extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::sfShl(parent, ap, bvSize, extractSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(se, ID_SF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::zf(Inst &inst,
                                   SymbolicElement *parent,
                                   AnalysisProcessor &ap,
                                   uint32 dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::zf(parent, bvSize);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_ZF, parent->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::zfShl(Inst &inst,
                                      SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32 dstSize,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32              bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::zfShl(parent, ap, bvSize, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(inst, expr, ID_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  ap.setTaintReg(se, ID_ZF, parent->isTainted);

  return se;
}

