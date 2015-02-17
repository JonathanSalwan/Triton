#include <boost/format.hpp>
#include <stdexcept>

#include "EflagsIRBuilder.h"
#include "Registers.h"


EflagsIRBuilder::EflagsIRBuilder()
{
}


EflagsIRBuilder::~EflagsIRBuilder()
{
}


//SymbolicElement *EflagsIRBuilder::af(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsIRBuilder::cf(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsIRBuilder::of(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsIRBuilder::pf(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}
//
//
//SymbolicElement *EflagsIRBuilder::sf(SymbolicElement *parent, AnalysisProcessor &ap) const
//{
//  // TODO
//}


SymbolicElement *EflagsIRBuilder::zf(SymbolicElement *parent, AnalysisProcessor &ap) const
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

