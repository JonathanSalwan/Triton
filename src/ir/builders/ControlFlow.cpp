#include <stdexcept>

#include <ControlFlow.h>
#include <Registers.h>



SymbolicExpression *ControlFlow::rip(Inst &inst, AnalysisProcessor &ap, uint64 nextAddr)
{
  SymbolicExpression    *se;
  std::stringstream   expr;

  /*
   * Create the SMT semantic.
   * RIP = nextAddress
   */
  expr << smt2lib::bv(nextAddr, 64);

  /* Create the symbolic expression */
  se = ap.createRegSE(inst, expr, ID_RIP, REG_SIZE, "RIP");

  return se;
}

