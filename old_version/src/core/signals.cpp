
#include "pin.H"
#include "Triton.h"
#include "Colors.h"


static VOID displayCurrentContext(CONTEXT *ctx)
{
  std::cout << _RED << "[SIGSEGV]=----------------------------------------------------------" << std::endl;
  std::cout << std::hex << std::internal << std::setfill('0') 
    << "RAX = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RAX) << " " 
    << "RBX = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RBX) << " " 
    << "RCX = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RCX) << std::endl
    << "RDX = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RDX) << " " 
    << "RDI = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RDI) << " " 
    << "RSI = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RSI) << std::endl
    << "RBP = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RBP) << " "
    << "RSP = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RSP) << " "
    << "RIP = " << std::setw(16) << PIN_GetContextReg(ctx, LEVEL_BASE::REG_RIP) << std::endl;
  std::cout << "+-------------------------------------------------------------------" << _ENDC << std::endl;
}

/* Callback for the SIGSEGV signal.
 * Display the context registers when a crash occurs */
BOOL catchSignal(THREADID tid, INT32 sig, CONTEXT *ctx, BOOL hasHandler, const EXCEPTION_INFO *pExceptInfo, VOID *v)
{
  std::cout << std::endl << std::endl << _RED << "/!\\ SIGSEGV received /!\\" << _ENDC << std::endl;
  displayCurrentContext(ctx);
  exit(1);
}

