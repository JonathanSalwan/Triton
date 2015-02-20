#include <boost/format.hpp>
#include <stdexcept>

#include "EflagsBuilder.h"
#include "Registers.h"


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
   * bvult : unsigned less than
   */
  expr << "(assert (bvult #" << std::dec << parent->getID() << " " << op1.str() << "))";

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_CF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


//SymbolicElement *EflagsBuilder::of(SymbolicElement *parent, AnalysisProcessor &ap)
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsBuilder::pf(SymbolicElement *parent, AnalysisProcessor &ap)
//{
//  // TODO
//}


SymbolicElement *EflagsBuilder::sf(SymbolicElement *parent, AnalysisProcessor &ap, uint32_t dstSize)
{
  SymbolicElement     *se;
  std::stringstream   expr;
  uint32_t            extractSize = (dstSize * 8) - 1;

  /* Create the SMT semantic. */
  expr << "(assert (= ((_ extract " << extractSize << " " << extractSize << ")#" << std::dec << parent->getID() << ") (_ bv1 1)))";

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_SF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}


SymbolicElement *EflagsBuilder::zf(SymbolicElement *parent, AnalysisProcessor &ap)
{
  SymbolicElement     *se;
  std::stringstream   expr;

  /* Create the SMT semantic */
  expr << "(assert (= #" << std::dec << parent->getID() << " 0))";

  /* Create the symbolic element */
  se = ap.createRegSE(expr, ID_ZF);

  /* Spread the taint from the parent to the child */
  se->isTainted = parent->isTainted;

  return se;
}

