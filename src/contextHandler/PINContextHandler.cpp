
#include <iostream>
#include <stdexcept>

#include <PINContextHandler.h>
#include <PINConverter.h>



PINContextHandler::PINContextHandler(CONTEXT *ctx, THREADID id):
  _ctx(ctx),
  _threadId(id)
{
}


// REG is a enum, so the cast is from a bigger type.
static inline REG safecast(uint64 regID)
{
  return static_cast<REG>(regID);
}

void *PINContextHandler::getCtx(void) const
{
  return this->_ctx;
}


// There is no verification on the validity of the ID.
uint64 PINContextHandler::getFlagValue(uint64 TritFlagID) const
{
  uint64 rflags;
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(ID_RFLAGS));

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
uint64 PINContextHandler::getRegisterValue(uint64 TritRegID) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: getRegisterValue() - Invalid PIN register id.");

  return PIN_GetContextReg(this->_ctx, reg);
}


// There is no verification on the validity of the ID.
uint128 PINContextHandler::getSSERegisterValue(uint64 TritRegID) const
{
  REG reg                 = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  uint128 value       = 0;
  PIN_REGISTER tmp;

  if (!REG_valid(reg) || !(TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: getSSERegisterValue() - Invalid PIN register id.");

  PIN_GetContextRegval(this->_ctx, reg, reinterpret_cast<uint8 *>(&tmp));

  value = *reinterpret_cast<uint128*>(&tmp);

  return value;
}


// There is no verification on the validity of the ID.
void PINContextHandler::setRegisterValue(uint64 TritRegID, uint64 value) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));

  if (!REG_valid(reg) || (TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: setRegisterValue() - Invalid PIN register id.");

  PIN_SetContextReg(this->_ctx, reg, value);
  PIN_ExecuteAt(this->_ctx);
}


// There is no verification on the validity of the ID.
void PINContextHandler::setSSERegisterValue(uint64 TritRegID, uint128 value) const
{
  REG reg = safecast(PINConverter::convertTritonReg2DBIReg(TritRegID));
  unsigned char *tmp      = (unsigned char*)malloc(16);

  if (tmp == nullptr)
    throw std::runtime_error("Error: setSSERegisterValue() - Not enough memory.");

  if (!REG_valid(reg) || !(TritRegID >= ID_XMM0 && TritRegID <= ID_XMM15))
    throw std::runtime_error("Error: setSSERegisterValue() - Invalid PIN register id.");

  *(uint128 *)tmp = value;

  PIN_SetContextRegval(this->_ctx, reg, tmp);
  PIN_ExecuteAt(this->_ctx);
  free(tmp);
}


/* Used to deref a pointer address and returns the targeted byte by size of read */
uint128 PINContextHandler::getMemValue(uint64 mem, uint32 readSize) const
{

  if (PIN_CheckReadAccess(reinterpret_cast<void*>(mem)) == false) {
    std::cout << "[Bugs] Invalid read at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(readSize){
    case BYTE_SIZE:   return static_cast<uint128>(*(reinterpret_cast<uint8 *>(mem)));
    case WORD_SIZE:   return static_cast<uint128>(*(reinterpret_cast<UINT16 *>(mem)));
    case DWORD_SIZE:  return static_cast<uint128>(*(reinterpret_cast<uint32 *>(mem)));
    case QWORD_SIZE:  return static_cast<uint128>(*(reinterpret_cast<uint64 *>(mem)));
    case DQWORD_SIZE: return static_cast<uint128>(*(reinterpret_cast<uint128 *>(mem)));
  }
  throw std::runtime_error("Error: PINContextHandler::getMemValue() - Invalid read size");
  return 0; // Never go there
}


/* Used to inject value into memory */
void PINContextHandler::setMemValue(uint64 mem, uint32 writeSize, uint128 value) const
{

  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(mem)) == false) {
    std::cout << "[Bugs] Invalid write at " << std::hex << mem << std::endl;
    exit(0);
  }

  switch(writeSize){
    case BYTE_SIZE:
      *((char *)mem) = value;
      break;
    case WORD_SIZE:
      *((short *)mem) = value;
      break;
    case DWORD_SIZE:
      *((uint32 *)mem) = value;
      break;
    case QWORD_SIZE:
      *((uint64 *)mem) = value;
      break;
    case DQWORD_SIZE:
      *((uint128 *)mem) = value;
      break;
    default:
      throw std::runtime_error("Error: PINContextHandler::setMemValue() - Invalid write size");
  }

}


/* Returns the thread id  */
uint32 PINContextHandler::getThreadID(void) const
{
  return this->_threadId;
}

