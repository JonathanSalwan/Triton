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
}


// REG is a enum, so the cast is from a bigger type.
static inline REG safecast(reg_size regID) {
  return static_cast<REG>(regID);
}

void *PINContextHandler::getCtx(void) const {
  return this->_ctx;
}


// There is no verification on the validity of the ID.
reg_size PINContextHandler::getFlagValue(reg_size TritFlagID) const {
  reg_size rflags;


  #if defined(__x86_64__) || defined(_M_X64)
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(ID_RFLAGS));
  #endif

  #if defined(__i386) || defined(_M_IX86)
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(ID_EFLAGS));
  #endif

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


// There is no verification on the validity of the ID.



reg_size PINContextHandler::getRegisterValue(reg_size TritRegID) const {
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));


  #if defined(__x86_64__) || defined(_M_X64)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15)){
  #endif

  #if defined(__i386) || defined(_M_IX86)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM7)){
  #endif  
    throw std::runtime_error("Error: getRegisterValue() - Invalid PIN register id.");
  }

  return PIN_GetContextReg(this->_ctx, reg);
}


// There is no verification on the validity of the ID.
uint128 PINContextHandler::getSSERegisterValue(reg_size TritRegID) const {
  REG reg                 = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  uint128 value       = 0;
  PIN_REGISTER tmp;

  #if defined(__x86_64__) || defined(_M_X64)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15)){
  #endif

  #if defined(__i386) || defined(_M_IX86)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM7)){
  #endif
    throw std::runtime_error("Error: getSSERegisterValue() - Invalid PIN register id.");
    }

  PIN_GetContextRegval(this->_ctx, reg, reinterpret_cast<uint8 *>(&tmp));

  value = *reinterpret_cast<uint128*>(&tmp);

  return value;
}


// There is no verification on the validity of the ID.
void PINContextHandler::setRegisterValue(reg_size TritRegID, reg_size value) const {
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

    #if defined(__x86_64__) || defined(_M_X64)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15)){
  #endif

  #if defined(__i386) || defined(_M_IX86)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM7)){
  #endif
    throw std::runtime_error("Error: setRegisterValue() - Invalid PIN register id.");
  }

  PIN_SetContextReg(this->_ctx, reg, value);
  PIN_UnlockClient();
  PIN_ExecuteAt(this->_ctx);
}


// There is no verification on the validity of the ID.
void PINContextHandler::setSSERegisterValue(reg_size TritRegID, uint128 value) const {
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  unsigned char *tmp      = (unsigned char*)malloc(16);

  if (tmp == nullptr)
    throw std::runtime_error("Error: setSSERegisterValue() - Not enough memory.");

  #if defined(__x86_64__) || defined(_M_X64)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15)){
  #endif

  #if defined(__i386) || defined(_M_IX86)
  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM7)){
  #endif
    throw std::runtime_error("Error: setSSERegisterValue() - Invalid PIN register id.");
  }

  *(uint128 *)tmp = value;

  PIN_SetContextRegval(this->_ctx, reg, tmp);
  PIN_UnlockClient();
  PIN_ExecuteAt(this->_ctx);
  free(tmp);
}


/* Used to deref a pointer address and returns the targeted byte by size of read */
uint128 PINContextHandler::getMemValue(reg_size mem, uint32 readSize) const {

  if (PIN_CheckReadAccess(reinterpret_cast<void*>(mem)) == false) {
    std::cout << "[Bugs] Invalid read at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(readSize){
    case BYTE_SIZE:   return static_cast<uint128>(*(reinterpret_cast<uint8 *>(mem)));
    case WORD_SIZE:   return static_cast<uint128>(*(reinterpret_cast<UINT16 *>(mem)));
    case DWORD_SIZE:  return static_cast<uint128>(*(reinterpret_cast<uint32 *>(mem)));
    case QWORD_SIZE:  return static_cast<uint128>(*(reinterpret_cast<reg_size *>(mem)));
    case DQWORD_SIZE: return static_cast<uint128>(*(reinterpret_cast<uint128 *>(mem)));
  }
  throw std::runtime_error("Error: PINContextHandler::getMemValue() - Invalid read size");
  return 0; // Never go there
}


/* Used to inject value into memory */
void PINContextHandler::setMemValue(reg_size mem, uint32 writeSize, uint128 value) const {

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
      *((reg_size *)mem) = boost::numeric_cast<reg_size>(value);
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

