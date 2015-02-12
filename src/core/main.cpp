#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <vector>

#include "pin.H"

#include "PINContextHandler.h"
#include "IRBuilder.h"
#include "IRBuilderFactory.h"
#include "trigger.h"


/* Pin options: -startAnalysis */
KNOB<std::string>  KnobStartAnalysis(KNOB_MODE_WRITEONCE, "pintool", "startAnalysis", "", "Start/end the analysis from a scope function");


Trigger analysisTrigger;


VOID callback(IRBuilder *irb, CONTEXT *ctx, BOOL hasEA, ADDRINT ea)
{
  if (!analysisTrigger.getState())
    // Analysis locked
    return;

  PINContextHandler ctxH(ctx);

  if (hasEA)
    irb->setup(ea);

  // TODO
  // Must take Trace (or SymbolicEngine/Taint) in arg and return a inst.
  // Must create the smt2lib and apply the taint.
  // Add taint method for each case Mem-Reg, Mem-Imm, Reg-Imm, Reg-Reg.

  // Can throw runtime_error
  shared_ptr<std::stringstream> expr(irb->process(ctxH));

  std::cout << *irb;

  if(expr)
    std::cout << " Expr: " << expr->str();

  std::cout << std::endl;

  // Add TritInst to Trace
}

VOID TRACE_Instrumentation(TRACE trace, VOID *v)
{
  for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl))
    for (INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)) {
      IRBuilder *irb = createIRBuilder(ins);

      if (INS_MemoryOperandCount(ins) > 0)
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callback,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, true,
            IARG_MEMORYOP_EA, 0,
            IARG_END);
      else
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callback,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, false,
            IARG_ADDRINT, 0,
            IARG_END);
      }
}


void toggleWrapper()
{
  analysisTrigger.toggle();
  std::cout << "Analysis:" << boolalpha << analysisTrigger.getState() << noboolalpha <<std::endl;
}


VOID IMG_Instrumentation(IMG img, VOID *)
{
  /* This callback is used to lock and target the analysis */
  /* Mainly used to target an area */
  RTN targetRTN = RTN_FindByName(img, KnobStartAnalysis.Value().c_str());
  if (RTN_Valid(targetRTN)){
    RTN_Open(targetRTN);
    RTN_InsertCall(targetRTN,
        IPOINT_BEFORE,
        (AFUNPTR) toggleWrapper,
        IARG_END);

    RTN_InsertCall(targetRTN,
        IPOINT_AFTER,
        (AFUNPTR) toggleWrapper,
        IARG_END);

    RTN_Close(targetRTN);
  }
}

// Usage function if Pin fail to start.
// Display the help message.
INT32 Usage()
{
  std::cerr << KNOB_BASE::StringKnobSummary() << std::endl;
  return -1;
}


int main(int argc, char *argv[])
{
  PIN_InitSymbols();
  if(PIN_Init(argc, argv)){
      return Usage();
  }

  // We first need a target function
  if (KnobStartAnalysis.Value().empty())
    return Usage();

  analysisTrigger = Trigger();

  // Enable Intel syntax
  PIN_SetSyntaxIntel();

  // Image callback
  IMG_AddInstrumentFunction(IMG_Instrumentation, NULL);

  // Instruction callback
  TRACE_AddInstrumentFunction(TRACE_Instrumentation, NULL);

  // Never returns
  PIN_StartProgram();

  return 0;
}
