#include <boost/format.hpp>
#include <stdexcept>

#include "EflagsBuilder.h"
#include "Registers.h"



SymbolicElement *EflagsBuilder::af(SymbolicElement *parent,
                                   AnalysisProcessor &ap,
                                   uint32_t dstSize,
                                   std::stringstream &op1,
                                   std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::af(parent, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_AF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::afNeg(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::afNeg(parent, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_AF, "Adjust flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_AF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfAdd(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::cfAdd(parent, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_CF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfNeg(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfNeg(bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_CF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfShl(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::cfShl(parent, ap, bvSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_CF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::cfSub(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::cfSub(op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_CF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::clearFlag(AnalysisProcessor &ap,
                                          regID_t flag)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::clearFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, flag);

  /* Spread the taint from the parent to the child */
  se->isTainted = !TAINTED;
  ap.setTaintReg(flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::clearFlag(AnalysisProcessor &ap,
                                          regID_t flag,
                                          std::string comment)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::clearFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, flag, comment);

  /* Spread the taint from the parent to the child */
  se->isTainted = !TAINTED;
  ap.setTaintReg(flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::ofAdd(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::ofAdd(parent, extractSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_OF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofNeg(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofNeg(parent, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_OF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofShl(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::ofShl(parent, ap, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_OF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::ofSub(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1,
                                      std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::ofSub(parent, extractSize, op1, op2);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_OF, "Overflow flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_OF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::pf(SymbolicElement *parent,
                                   AnalysisProcessor &ap)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::pf(parent);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_PF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::pfShl(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::pfShl(parent, ap, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_PF, "Parity flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_PF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::setFlag(AnalysisProcessor &ap,
                                        regID_t flag)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::setFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, flag);

  /* Spread the taint from the parent to the child */
  se->isTainted = !TAINTED;
  ap.setTaintReg(flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::setFlag(AnalysisProcessor &ap,
                                        regID_t flag,
                                        std::string comment)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << EflagsExpressions::setFlag();

  /* Create the symbolic element */
  se = ap.createRegSE(expr, flag, comment);

  /* Spread the taint from the parent to the child */
  se->isTainted = !TAINTED;
  ap.setTaintReg(flag, !TAINTED);

  return se;
}


SymbolicElement *EflagsBuilder::sf(SymbolicElement *parent,
                                   AnalysisProcessor &ap,
                                   uint32_t dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::sf(parent, extractSize);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_SF, "Sign flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_SF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::sfShl(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);
  uint32_t            extractSize = (dstSize * REG_SIZE) - 1;

  expr << EflagsExpressions::sfShl(parent, ap, bvSize, extractSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF, "Carry flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_CF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::zf(SymbolicElement *parent,
                                   AnalysisProcessor &ap,
                                   uint32_t dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::zf(parent, bvSize);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_ZF, se->isTainted);

  return se;
}


SymbolicElement *EflagsBuilder::zfShl(SymbolicElement *parent,
                                      AnalysisProcessor &ap,
                                      uint32_t dstSize,
                                      std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            bvSize = (dstSize * REG_SIZE);

  expr << EflagsExpressions::zfShl(parent, ap, bvSize, op1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_ZF, "Zero flag");

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;
  ap.setTaintReg(ID_ZF, se->isTainted);

  return se;
}
