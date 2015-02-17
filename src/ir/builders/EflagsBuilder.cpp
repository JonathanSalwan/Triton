#include <boost/format.hpp>
#include <stdexcept>

#include "EflagsBuilder.h"
#include "Registers.h"


//SymbolicElement *EflagsBuilder::af(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsBuilder::cf(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsBuilder::of(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsBuilder::pf(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsBuilder::sf(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}


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

