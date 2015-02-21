#include <boost/format.hpp>
#include <stdexcept>

#include "EflagsBuilder.h"
#include "Registers.h"


// R_AF:bool = 0x10:u64 == (0x10:u64 & (R_RBX:u64 ^ T_t1:u64 ^ T_t2:u64))
//
//SymbolicElement *EflagsBuilder::af(SymbolicElement *parent, AnalysisProcessor &ap)
//{
//  // TODO
//}


SymbolicElement *EflagsBuilder::cf(SymbolicElement *parent, AnalysisProcessor &ap, std::stringstream &op1)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  /*
   * Create the SMT semantic.
   * cf = regDst < op1
   */
  expr << smt2lib::smtAssert(
            smt2lib::bvult(
              parent->getID2Str(),
              op1.str()
            )
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::of(SymbolicElement *parent,
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
  expr << smt2lib::smtAssert(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize,
                smt2lib::bvand(
                  smt2lib::bvxor(op1.str(), smt2lib::bvnot(op2.str())),
                  smt2lib::bvxor(op1.str(), parent->getID2Str())
                )
              ),
              smt2lib::bv(1, 1)
            )
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
  expr << smt2lib::smtAssert(
            smt2lib::equal(
              smt2lib::parityFlag(
                smt2lib::extract(7, 0, parent->getID2Str())),
              smt2lib::bv(0, 1)
            )
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
  expr << smt2lib::smtAssert(
            smt2lib::equal(
              smt2lib::extract(extractSize, extractSize, parent->getID2Str()),
              smt2lib::bv(1, 1)
            )
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
  expr << smt2lib::smtAssert(
            smt2lib::equal(
              parent->getID2Str(),
              smt2lib::bv(0, dstSize * REG_SIZE)
            )
          );

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_ZF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}

