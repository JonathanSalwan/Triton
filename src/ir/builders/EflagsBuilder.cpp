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

  /*
   * Create the SMT semantic.
   * af = 0x10 == (0x10 & (regDst ^ op1 ^ op2))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::bv(0x10, bvSize),
              smt2lib::bvand(
                smt2lib::bv(0x10, bvSize),
                smt2lib::bvxor(
                  parent->getID2Str(),
                  smt2lib::bvxor(op1.str(), op2.str())
                )
              )
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_AF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::cfAdd(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  /*
   * Create the SMT semantic.
   * cf = regDst < op1
   */
  expr << smt2lib::ite(
            smt2lib::bvult(
              parent->getID2Str(),
              op1.str()
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::cfSub(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1, std::stringstream &op2)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  /*
   * Create the SMT semantic.
   * cf = op1 < op2
   */
  expr << smt2lib::ite(
            smt2lib::bvult(
              op1.str(),
              op2.str()
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::clearFlag(AnalysisProcessor &ap, regID_t flag)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  expr << smt2lib::bv(0, 1);

  /* Create the symbolic element */
  se = ap.createRegSE(expr, flag);

  /* Spread the taint from the parent to the child */
  se->isTainted = !TAINTED;

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

  /*
   * Create the SMT semantic.
   * of = high:bool((op1 ^ ~op2) & (op1 ^ regDst))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1.str(), smt2lib::bvnot(op2.str())),
                  smt2lib::bvxor(op1.str(), parent->getID2Str())
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_OF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

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

  /*
   * Create the SMT semantic.
   * of = high:bool((op1 ^ op2) & (op1 ^ regDst))
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1.str(), op2.str()),
                  smt2lib::bvxor(op1.str(), parent->getID2Str())
                )
              ),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_OF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::pf(SymbolicElement *parent, AnalysisProcessor &ap)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  /*
   * Create the SMT semantic.
   *
   * pf is set to one if there is a even number of bit set to 1 in the least
   * significant byte of the result.
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::parityFlag(
                smt2lib::extract(7, 0, parent->getID2Str())),
              smt2lib::bv(0, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_PF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::sf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            extractSize = (dstSize * REG_SIZE) - 1;

  /*
   * Create the SMT semantic.
   * sf = high:bool(regDst)
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize, parent->getID2Str()),
              smt2lib::bv(1, 1)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_SF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::zf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  /*
   * Create the SMT semantic.
   * zf = 0 == regDst
   */
  expr << smt2lib::ite(
            smt2lib::equal(
              parent->getID2Str(),
              smt2lib::bv(0, dstSize * REG_SIZE)
            ),
            smt2lib::bv(1, 1),
            smt2lib::bv(0, 1)
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_ZF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}

