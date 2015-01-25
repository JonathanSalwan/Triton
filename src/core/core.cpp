
#include "pin.H"
#include "triton.h"


/* Pin options */
KNOB<std::string>  KnobStartAnalysis(KNOB_MODE_WRITEONCE, "pintool", "startAnalysis", "none", "Start analysis from a function name");

/* flag Lock / Unlock instrumentation */
UINT32 _analysisStatus = LOCKED;

/* symbolic expression ID */
UINT64 uniqueID;

/* Number of symbolic variables used */
UINT64 numberOfSymVar = 0;

/* Addresses tainted */
std::list<UINT64> addressesTainted;

/* 
 * Addresses <-> symbolic expression 
 * item1: memory address
 * item2: reference ID
 */
std::list< std::pair<UINT64, UINT64> > memoryReference;

/*
 * Addresses <-> Z3 Symbolic Variable
 * item1: memory address
 * item2: symbolic variable ID
 */
std::list< std::pair<UINT64, UINT64> > symVarMemoryReference;

/* I/O memory monitoring for snapshot */
std::list< std::pair<UINT64, UINT8> > memorySnapshot;

/* List of symbolic elements ID */
std::list<symbolicElement *> symbolicList;

/* Output */
boost::format outputInstruction("%1% %|15t| %2% %|55t| %3% %|90t| %4%\n");

/* Symbolic trace */
UINT64 symbolicReg[] = {
    (UINT64)-1, /* ID_RAX   */
    (UINT64)-1, /* ID_RBX   */
    (UINT64)-1, /* ID_RCX   */
    (UINT64)-1, /* ID_RDX   */
    (UINT64)-1, /* ID_RDI   */
    (UINT64)-1, /* ID_RSI   */
    (UINT64)-1, /* ID_RBP   */
    (UINT64)-1, /* ID_RSP   */
    (UINT64)-1, /* ID_R8    */
    (UINT64)-1, /* ID_R9    */
    (UINT64)-1, /* ID_R10   */
    (UINT64)-1, /* ID_R11   */
    (UINT64)-1, /* ID_R12   */
    (UINT64)-1, /* ID_R13   */
    (UINT64)-1, /* ID_R14   */
    (UINT64)-1, /* ID_R15   */
    (UINT64)-1, /* ID_CF    */
    (UINT64)-1, /* ID_PF    */
    (UINT64)-1, /* ID_AF    */
    (UINT64)-1, /* ID_ZF    */
    (UINT64)-1, /* ID_SF    */
    (UINT64)-1, /* ID_TF    */
    (UINT64)-1, /* ID_IF    */
    (UINT64)-1, /* ID_DF    */
    (UINT64)-1  /* ID_OF    */
};

/* Registers tainted monitoring */
UINT64 taintedReg[] = {
    (UINT64)0, /* ID_RAX    */
    (UINT64)0, /* ID_RBX    */
    (UINT64)0, /* ID_RCX    */
    (UINT64)0, /* ID_RDX    */
    (UINT64)0, /* ID_RDI    */
    (UINT64)0, /* ID_RSI    */
    (UINT64)0, /* ID_RBP    */
    (UINT64)0, /* ID_RSP    */
    (UINT64)0, /* ID_R8     */
    (UINT64)0, /* ID_R9     */
    (UINT64)0, /* ID_R10    */
    (UINT64)0, /* ID_R11    */
    (UINT64)0, /* ID_R12    */
    (UINT64)0, /* ID_R13    */
    (UINT64)0, /* ID_R14    */
    (UINT64)0, /* ID_R15    */
};


INT32 Usage()
{
    cerr << KNOB_BASE::StringKnobSummary() << endl;
    return -1;
}


int main(int argc, char *argv[])
{
  PIN_InitSymbols();
  if(PIN_Init(argc, argv)){
      return Usage();
  }
 
  if (KnobStartAnalysis.Value().empty())
    return Usage();

  PIN_SetSyntaxIntel();
  IMG_AddInstrumentFunction(Image, 0);
  INS_AddInstrumentFunction(Instruction, 0);
  PIN_StartProgram();

  return 0;
}

