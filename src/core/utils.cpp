
#include "pin.H"

#include "registers.h"
#include "utils.h"


/* In some cases, we need to convert Pin registers to your own ID
 * Mainly used in the Taint and the Symbolic engine */
UINT64 translatePinRegToID(REG reg)
{
  switch(reg){
    case REG_RAX:
    case REG_EAX:
    case REG_AX:
    case REG_AH:
    case REG_AL:
         return ID_RAX;

    case REG_RBX:
    case REG_EBX:
    case REG_BX:
    case REG_BH:
    case REG_BL:
         return ID_RBX;

    case REG_RCX:
    case REG_ECX:
    case REG_CX:
    case REG_CH:
    case REG_CL:
         return ID_RCX;

    case REG_RDX:
    case REG_EDX:
    case REG_DX:
    case REG_DH:
    case REG_DL:
         return ID_RDX;

    case REG_RDI:
    case REG_EDI:
    case REG_DI:
    case REG_DIL:
         return ID_RDI;

    case REG_RSI:
    case REG_ESI:
    case REG_SI:
    case REG_SIL:
         return ID_RSI;

    case REG_RBP:
    case REG_EBP:
    case REG_BP:
         return ID_RBP;

    case REG_RSP:
    case REG_ESP:
    case REG_SP:
         return ID_RSP;

    case REG_R8:
    case REG_R8D:
    case REG_R8W:
    case REG_R8B:
         return ID_R8;

    case REG_R9:
    case REG_R9D:
    case REG_R9W:
    case REG_R9B:
         return ID_R9;

    case REG_R10:
    case REG_R10D:
    case REG_R10W:
    case REG_R10B:
         return ID_R10;

    case REG_R11:
    case REG_R11D:
    case REG_R11W:
    case REG_R11B:
         return ID_R11;

    case REG_R12:
    case REG_R12D:
    case REG_R12W:
    case REG_R12B:
         return ID_R12;

    case REG_R13:
    case REG_R13D:
    case REG_R13W:
    case REG_R13B:
         return ID_R13;

    case REG_R14:
    case REG_R14D:
    case REG_R14W:
    case REG_R14B:
         return ID_R14;

    case REG_R15:
    case REG_R15D:
    case REG_R15W:
    case REG_R15B:
         return ID_R15;

    default:
      return -1;
  }
}

/* In some cases, Pin need the Highest size register like
 * the PIN_GetContextReg() function */
REG getHighReg(REG reg)
{
  switch(reg){
    case REG_RAX:
    case REG_EAX:
    case REG_AX:
    case REG_AH:
    case REG_AL:
         return REG_RAX;

    case REG_RBX:
    case REG_EBX:
    case REG_BX:
    case REG_BH:
    case REG_BL:
         return REG_RBX;

    case REG_RCX:
    case REG_ECX:
    case REG_CX:
    case REG_CH:
    case REG_CL:
         return REG_RCX;

    case REG_RDX:
    case REG_EDX:
    case REG_DX:
    case REG_DH:
    case REG_DL:
         return REG_RDX;

    case REG_RDI:
    case REG_EDI:
    case REG_DI:
    case REG_DIL:
         return REG_RDI;

    case REG_RSI:
    case REG_ESI:
    case REG_SI:
    case REG_SIL:
         return REG_RSI;

    case REG_RBP:
    case REG_EBP:
    case REG_BP:
         return REG_RBP;

    case REG_RSP:
    case REG_ESP:
    case REG_SP:
         return REG_RSP;

    case REG_R8:
    case REG_R8D:
    case REG_R8W:
    case REG_R8B:
         return REG_R8;

    case REG_R9:
    case REG_R9D:
    case REG_R9W:
    case REG_R9B:
         return REG_R9;

    case REG_R10:
    case REG_R10D:
    case REG_R10W:
    case REG_R10B:
         return REG_R10;

    case REG_R11:
    case REG_R11D:
    case REG_R11W:
    case REG_R11B:
         return REG_R11;

    case REG_R12:
    case REG_R12D:
    case REG_R12W:
    case REG_R12B:
         return REG_R12;

    case REG_R13:
    case REG_R13D:
    case REG_R13W:
    case REG_R13B:
         return REG_R13;

    case REG_R14:
    case REG_R14D:
    case REG_R14W:
    case REG_R14B:
         return REG_R14;

    case REG_R15:
    case REG_R15D:
    case REG_R15W:
    case REG_R15B:
         return REG_R15;

    default:
      return REG_AL; /* hack exception */
  }
}

/* Unlock analysis. This is the -startAnalysis Pin option */
VOID unlockAnalysis(UINT32 *analysisStatus)
{
  *analysisStatus = UNLOCKED;
  std::cout << "[Start analysis]" << std::endl;
}


/* Unlock analysis. This is the -startAnalysis Pin option */
VOID lockAnalysis(UINT32 *analysisStatus)
{
  *analysisStatus = LOCKED;
  std::cout << "[Stop analysis]" << std::endl;
}


/* TODO: Must be deleted but currently used for test */
VOID taintParams(CONTEXT *ctx, TaintEngine *taintEngine)
{
  UINT64  i;
  ADDRINT rdi = PIN_GetContextReg(ctx, REG_RDI);
  char    *ptr = (char *)rdi;

  for (i = 0; ptr[i] != '\0'; i++){
    taintEngine->addAddress((ADDRINT)(&ptr[i]));
    std::cout << "[Initial tainting] *(" << std::hex << (ADDRINT)(&ptr[i]) << ") is now tainted" << std::endl;
  }
}

/* Used to deref a pointer address and returns the targeted byte by size of read */
UINT64 derefMem(UINT64 mem, UINT64 readSize)
{
  switch(readSize){
    case 1:
      return static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem)));
    case 2:
      return static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem)));
    case 4:
      return static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem)));
    case 8:
      return static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem)));
  }
  return 0; /* Never go here */
}


