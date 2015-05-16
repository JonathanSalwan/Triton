
#include <iostream>
#include <stdexcept>
#include <sys/mman.h>
#include <unistd.h>

#include "PINContextHandler.h"
#include "PINConverter.h"



PINContextHandler::PINContextHandler(CONTEXT *ctx, THREADID id):
  _ctx(ctx),
  _threadId(id)
{
}


// REG is a enum, so the cast is from a bigger type.
static inline REG safecast(uint64_t regID)
{
  return static_cast<REG>(regID);
}

void *PINContextHandler::getCtx(void) const
{
  return this->_ctx;
}


// There is no verification on the validity of the ID.
uint64_t PINContextHandler::getFlagValue(uint64_t TritFlagID) const
{
  uint64_t rflags;
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(ID_RFLAGS));

  if (reg == -1 || !REG_valid(reg))
    throw std::runtime_error("Error: Invalid PIN register id.");

  rflags = PIN_GetContextReg(this->_ctx, reg);

  switch (TritFlagID){
    case ID_AF: return (rflags >> 4) & 1;
    case ID_CF: return rflags & 1;
    case ID_DF: return (rflags >> 10) & 1;
    case ID_IF: return (rflags >> 9) & 1;
    case ID_OF: return (rflags >> 11) & 1;
    case ID_PF: return (rflags >> 2) & 1;
    case ID_SF: return (rflags >> 7) & 1;
    case ID_TF: return (rflags >> 8) & 1;
    case ID_ZF: return (rflags >> 6) & 1;
    default:
      throw std::runtime_error("Error: Invalid Flag id.");
  }
  return 0;
}


// There is no verification on the validity of the ID.
uint64_t PINContextHandler::getRegisterValue(uint64_t TritRegID) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

  if (reg == -1 || !REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: Invalid PIN register id.");

  return PIN_GetContextReg(this->_ctx, reg);
}


// There is no verification on the validity of the ID.
__uint128_t PINContextHandler::getSSERegisterValue(uint64_t TritRegID) const
{
  REG reg                 = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  __uint128_t value       = 0;
  PIN_REGISTER tmp;

  if (reg == -1 || !REG_valid(reg) || !(TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: Invalid PIN register id.");

  PIN_GetContextRegval(this->_ctx, reg, reinterpret_cast<UINT8 *>(&tmp));

  value = *reinterpret_cast<__uint128_t*>(&tmp);

  return value;
}


// There is no verification on the validity of the ID.
void PINContextHandler::setRegisterValue(uint64_t TritRegID, uint64_t value) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

  if (reg == -1 || !REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: Invalid PIN register id.");

  PIN_SetContextReg(this->_ctx, reg, value);
  PIN_ExecuteAt(this->_ctx);
}


// There is no verification on the validity of the ID.
void PINContextHandler::setSSERegisterValue(uint64_t TritRegID, __uint128_t value) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  unsigned char *tmp      = (unsigned char*)malloc(16);

  if (tmp == nullptr)
    throw std::runtime_error("Error: Not enough memory.");

  if (reg == -1 || !REG_valid(reg) || !(TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: Invalid PIN register id.");

  *(__uint128_t *)tmp = value;

  PIN_SetContextRegval(this->_ctx, reg, tmp);
  PIN_ExecuteAt(this->_ctx);
  free(tmp);
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
__uint128_t PINContextHandler::getMemValue(uint64_t mem, uint32_t readSize) const
{

  if (!isAddressMapped(mem)){
    std::cout << "[Bugs] Invalid read at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(readSize){
    case 1:  return static_cast<__uint128_t>(*(reinterpret_cast<UINT8 *>(mem)));
    case 2:  return static_cast<__uint128_t>(*(reinterpret_cast<UINT16 *>(mem)));
    case 4:  return static_cast<__uint128_t>(*(reinterpret_cast<UINT32 *>(mem)));
    case 8:  return static_cast<__uint128_t>(*(reinterpret_cast<UINT64 *>(mem)));
    case 16: return static_cast<__uint128_t>(*(reinterpret_cast<__uint128_t *>(mem)));
  }
  throw std::runtime_error("Error: Invalid read size");
  return 0; // Never go there
}


/* Returns the thread id  */
uint32_t PINContextHandler::getThreadID(void) const
{
  return this->_threadId;
}

