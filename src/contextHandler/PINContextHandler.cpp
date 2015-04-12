
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


// There is no verification on the validity of the ID.
uint64_t PINContextHandler::getRegisterValue(uint64_t TritRegID) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  return PIN_GetContextReg(_ctx, reg);
}


uint64_t PINContextHandler::getRegisterSize(uint64_t TritRegID) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  return REG_Size(reg);
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


/* Returns the thread id  */
uint32_t PINContextHandler::getThreadID(void) const
{
  return this->_threadId;
}

