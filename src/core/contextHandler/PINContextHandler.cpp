/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <iostream>
#include <stdexcept>

#include <PINContextHandler.h>
#include <PINConverter.h>



PINContextHandler::PINContextHandler(CONTEXT *ctx, THREADID id):
  _ctx(ctx),
  _threadId(id) {
  this->mustBeExecuted = false;
}


/* REG is a enum, so the cast is from a bigger type. */
static inline REG safecast(__uint regID) {
  return static_cast<REG>(regID);
}


/* Returns the current context */
void *PINContextHandler::getCtx(void) const {
  return this->_ctx;
}


/* There is no verification on the validity of the ID. */
__uint PINContextHandler::getFlagValue(__uint TritFlagID) const {
  __uint rflags;
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(ID_FLAGS));

  if (!REG_valid(reg))
    throw std::runtime_error("Error: getFlagValue() - Invalid PIN register id.");

  rflags = PIN_GetContextReg(this->_ctx, reg);

  switch (TritFlagID){
    case ID_AF: return (rflags >> 4) & 1;
    case ID_CF: return (rflags & 1);
    case ID_DF: return (rflags >> 10) & 1;
    case ID_IF: return (rflags >> 9) & 1;
    case ID_OF: return (rflags >> 11) & 1;
    case ID_PF: return (rflags >> 2) & 1;
    case ID_SF: return (rflags >> 7) & 1;
    case ID_TF: return (rflags >> 8) & 1;
    case ID_ZF: return (rflags >> 6) & 1;
    default:
      throw std::runtime_error("Error: getFlagValue() - Invalid Flag id.");
  }
  return 0;
}


/* There is no verification on the validity of the ID. */
__uint PINContextHandler::getRegisterValue(__uint TritRegID) const {
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

  if (!REG_valid(reg) || isSSERegId(TritRegID))
    throw std::runtime_error("Error: getRegisterValue() - Invalid PIN register id.");

  return PIN_GetContextReg(this->_ctx, reg);
}


/* There is no verification on the validity of the ID. */
uint128 PINContextHandler::getSSERegisterValue(__uint TritRegID) const {
  REG reg       = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  uint128 value = 0;

  if (!REG_valid(reg) || !isSSERegId(TritRegID))
    throw std::runtime_error("Error: getSSERegisterValue() - Invalid PIN register id.");

  PIN_GetContextRegval(this->_ctx, reg, reinterpret_cast<uint8 *>(&value));

  return value;
}


/* There is no verification on the validity of the ID. */
void PINContextHandler::setRegisterValue(__uint TritRegID, __uint value) {
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

  if (!REG_valid(reg) || isSSERegId(TritRegID))
    throw std::runtime_error("Error: setRegisterValue() - Invalid PIN register id.");

  PIN_SetContextReg(this->_ctx, reg, value);
  this->mustBeExecuted = true;
}


/* There is no verification on the validity of the ID. */
void PINContextHandler::setSSERegisterValue(__uint TritRegID, uint128 value) {
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  unsigned char *tmp = (unsigned char*)malloc(16);

  if (tmp == nullptr)
    throw std::runtime_error("Error: setSSERegisterValue() - Not enough memory.");

  if (!REG_valid(reg) || !isSSERegId(TritRegID))
    throw std::runtime_error("Error: setSSERegisterValue() - Invalid PIN register id.");

  *(uint128 *)tmp = value;

  PIN_SetContextRegval(this->_ctx, reg, tmp);
  this->mustBeExecuted = true;
  free(tmp);
}


/* Used to deref a pointer address and returns the targeted byte by size of read */
uint128 PINContextHandler::getMemValue(__uint mem, uint32 readSize) const {

  if (PIN_CheckReadAccess(reinterpret_cast<void*>(mem)) == false) {
    std::cout << "[Bugs] Invalid read at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(readSize){
    case BYTE_SIZE:   return static_cast<uint128>(*(reinterpret_cast<uint8 *>(mem)));
    case WORD_SIZE:   return static_cast<uint128>(*(reinterpret_cast<UINT16 *>(mem)));
    case DWORD_SIZE:  return static_cast<uint128>(*(reinterpret_cast<uint32 *>(mem)));
    case QWORD_SIZE:  return static_cast<uint128>(*(reinterpret_cast<__uint *>(mem)));
    case DQWORD_SIZE: return static_cast<uint128>(*(reinterpret_cast<uint128 *>(mem)));
  }
  throw std::runtime_error("Error: PINContextHandler::getMemValue() - Invalid read size");
  return 0; // Never go there
}


/* Used to inject value into memory */
void PINContextHandler::setMemValue(__uint mem, uint32 writeSize, uint128 value) const {

  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(mem)) == false) {
    std::cout << "[Bugs] Invalid write at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(writeSize){
    case BYTE_SIZE:
      *((char *)mem) = boost::numeric_cast<char>(value);
      break;
    case WORD_SIZE:
      *((short *)mem) = boost::numeric_cast<short>(value);
      break;
    case DWORD_SIZE:
      *((uint32 *)mem) = boost::numeric_cast<uint32>(value);
      break;
    case QWORD_SIZE:
      *((__uint *)mem) = boost::numeric_cast<__uint>(value);
      break;
    case DQWORD_SIZE:
      *((uint128 *)mem) = value;
      break;
    default:
      throw std::runtime_error("Error: PINContextHandler::setMemValue() - Invalid write size");
  }

}


/* Returns the thread id  */
uint32 PINContextHandler::getThreadID(void) const {
  return this->_threadId;
}


/* Check if we must execute the context */
bool PINContextHandler::isMustBeExecuted(void) const {
  return this->mustBeExecuted;
}


/* Setup the context flag */
void PINContextHandler::setExecutedFlag(bool flag) {
  this->mustBeExecuted = flag;
}


/* Execute the context */
void PINContextHandler::executeContext(void) {
  if (this->mustBeExecuted == true) {
    this->mustBeExecuted = false;
    PIN_UnlockClient();
    PIN_ExecuteAt(this->_ctx);
  }
}

