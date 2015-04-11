#include "PINContextHandler.h"

#include <iostream>
#include <stdexcept>
#include <sys/mman.h>
#include <unistd.h>

PINContextHandler::PINContextHandler(CONTEXT *ctx, THREADID id): _ctx(ctx), _threadId(id) { }


/* In some cases, Pin need the Highest size register like
 * the PIN_GetContextReg() function */
static REG getHighReg(REG reg)
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
    case REG_BPL:
      return REG_RBP;

    case REG_RSP:
    case REG_ESP:
    case REG_SP:
    case REG_SPL:
      return REG_RSP;

    case REG_RIP:
    case REG_EIP:
    case REG_IP:
      return REG_RIP;

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
      throw std::runtime_error("Invalid REG ID");
  }
}

// REG is a enum, so the cast is from a bigger type.
static inline REG safecast(uint64_t regID)
{
  return static_cast<REG>(regID);
}

// There is no verification on the validity of the ID.
uint64_t PINContextHandler::getRegisterValue(uint64_t regID) const
{
  return PIN_GetContextReg(_ctx, getHighReg(safecast(regID)));
}

uint64_t PINContextHandler::getRegisterSize(uint64_t regID) const
{
  return REG_Size(safecast(regID));
}

/* Tricks to check if the address is mapped */
static bool isAddressMapped(ADDRINT addr) {
  int pagesize = getpagesize();
  void *foo = (void *)(addr / pagesize * pagesize);
  if (munlock(foo, 1) == -1)
    return false;
  return true;
}

/* Used to deref a pointer address and returns the targeted byte by size of read */
uint64_t PINContextHandler::getMemValue(uint64_t mem, uint32_t readSize) const
{

  if (!isAddressMapped(mem)){
    std::cout << "[Bugs] Invalid read at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(readSize){
    case 1: return static_cast<UINT64>(*(reinterpret_cast<UINT8 *>(mem)));
    case 2: return static_cast<UINT64>(*(reinterpret_cast<UINT16 *>(mem)));
    case 4: return static_cast<UINT64>(*(reinterpret_cast<UINT32 *>(mem)));
    case 8: return static_cast<UINT64>(*(reinterpret_cast<UINT64 *>(mem)));
  }
  throw std::runtime_error("Error: Invalid read size");
  return 0; // Never go there
}

// In some cases, we need to convert Pin registers to your own ID
// Mainly used in the Taint and the Symbolic engine.
uint64_t PINContextHandler::translateRegID(uint64_t regID) const
{
  switch(regID){
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
    case REG_BPL:
      return ID_RBP;

    case REG_RSP:
    case REG_ESP:
    case REG_SP:
    case REG_SPL:
      return ID_RSP;

    case REG_RIP:
    case REG_EIP:
    case REG_IP:
      return ID_RIP;

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

// Convert a Triton register to a Pin register
uint64_t PINContextHandler::convertTritonReg2PinReg(uint64_t regID) const
{
  switch(regID){
    case ID_RAX:   return REG_RAX;
    case ID_RBX:   return REG_RBX;
    case ID_RCX:   return REG_RCX;
    case ID_RDI:   return REG_RDI;
    case ID_RSI:   return REG_RSI;
    case ID_RBP:   return REG_RBP;
    case ID_RSP:   return REG_RSP;
    case ID_RIP:   return REG_RIP;
    case ID_R8:    return REG_R8;
    case ID_R9:    return REG_R9;
    case ID_R10:   return REG_R10;
    case ID_R11:   return REG_R11;
    case ID_R12:   return REG_R12;
    case ID_R13:   return REG_R13;
    case ID_R14:   return REG_R14;
    case ID_R15:   return REG_R15;
    case ID_XMM0:  return REG_XMM0;
    case ID_XMM1:  return REG_XMM1;
    case ID_XMM2:  return REG_XMM2;
    case ID_XMM3:  return REG_XMM3;
    case ID_XMM4:  return REG_XMM4;
    case ID_XMM5:  return REG_XMM5;
    case ID_XMM6:  return REG_XMM6;
    case ID_XMM7:  return REG_XMM7;
    case ID_XMM8:  return REG_XMM8;
    case ID_XMM9:  return REG_XMM9;
    case ID_XMM10: return REG_XMM10;
    case ID_XMM11: return REG_XMM11;
    case ID_XMM12: return REG_XMM12;
    case ID_XMM13: return REG_XMM13;
    case ID_XMM14: return REG_XMM14;
    case ID_XMM15: return REG_XMM15;
    default: return -1;
  }
}


/* Returns the thread id  */
THREADID PINContextHandler::getThreadID(void) const
{
  return this->_threadId;
}

