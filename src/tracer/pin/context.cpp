//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

/* libTriton */
#include <cpuSize.hpp>
#include <x86Specifications.hpp>

/* pintool */
#include "bindings.hpp"
#include "context.hpp"



namespace tracer {
  namespace pintool {
    namespace context {

      CONTEXT* lastContext    = nullptr;
      bool     mustBeExecuted = false;


      triton::uint128 getCurrentRegisterValue(triton::arch::RegisterOperand& reg) {
        unsigned char *tmp = (unsigned char*)malloc(DQWORD_SIZE);
        memset(tmp, 0x00, DQWORD_SIZE);

        #if defined(__x86_64__) || defined(_M_X64)
          switch (reg.getParent().getId()) {
            case triton::arch::x86::ID_REG_RAX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RAX, tmp);    break;
            case triton::arch::x86::ID_REG_RBX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBX, tmp);    break;
            case triton::arch::x86::ID_REG_RCX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RCX, tmp);    break;
            case triton::arch::x86::ID_REG_RDX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDX, tmp);    break;
            case triton::arch::x86::ID_REG_RDI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDI, tmp);    break;
            case triton::arch::x86::ID_REG_RSI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSI, tmp);    break;
            case triton::arch::x86::ID_REG_RBP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBP, tmp);    break;
            case triton::arch::x86::ID_REG_RSP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSP, tmp);    break;
            case triton::arch::x86::ID_REG_RIP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RIP, tmp);    break;
            case triton::arch::x86::ID_REG_RFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, tmp); break;
            case triton::arch::x86::ID_REG_R8:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8, tmp);     break;
            case triton::arch::x86::ID_REG_R9:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9, tmp);     break;
            case triton::arch::x86::ID_REG_R10:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10, tmp);    break;
            case triton::arch::x86::ID_REG_R11:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11, tmp);    break;
            case triton::arch::x86::ID_REG_R12:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12, tmp);    break;
            case triton::arch::x86::ID_REG_R13:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13, tmp);    break;
            case triton::arch::x86::ID_REG_R14:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14, tmp);    break;
            case triton::arch::x86::ID_REG_R15:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15, tmp);    break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0, tmp);   break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1, tmp);   break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2, tmp);   break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3, tmp);   break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4, tmp);   break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5, tmp);   break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6, tmp);   break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7, tmp);   break;
            case triton::arch::x86::ID_REG_XMM8:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM8, tmp);   break;
            case triton::arch::x86::ID_REG_XMM9:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM9, tmp);   break;
            case triton::arch::x86::ID_REG_XMM10:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM10, tmp);  break;
            case triton::arch::x86::ID_REG_XMM11:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM11, tmp);  break;
            case triton::arch::x86::ID_REG_XMM12:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM12, tmp);  break;
            case triton::arch::x86::ID_REG_XMM13:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM13, tmp);  break;
            case triton::arch::x86::ID_REG_XMM14:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM14, tmp);  break;
            case triton::arch::x86::ID_REG_XMM15:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM15, tmp);  break;
            default:
              if (reg.isFlag())
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, tmp);
              else
                throw std::runtime_error("tracer::pintool::getCurrentRegisterValue(): Invalid register.");
              break;
          }

        /* Sync with the libTriton */
        triton::arch::RegisterOperand syncReg;
        if (reg.isFlag())
          syncReg = TRITON_X86_REG_RFLAGS;
        else
          syncReg = reg.getParent();

        #endif

        #if defined(__i386) || defined(_M_IX86)
          switch (reg.getParent().getId()) {
            case triton::arch::x86::ID_REG_EAX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EAX, tmp);    break;
            case triton::arch::x86::ID_REG_EBX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBX, tmp);    break;
            case triton::arch::x86::ID_REG_ECX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ECX, tmp);    break;
            case triton::arch::x86::ID_REG_EDX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDX, tmp);    break;
            case triton::arch::x86::ID_REG_EDI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDI, tmp);    break;
            case triton::arch::x86::ID_REG_ESI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESI, tmp);    break;
            case triton::arch::x86::ID_REG_EBP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBP, tmp);    break;
            case triton::arch::x86::ID_REG_ESP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESP, tmp);    break;
            case triton::arch::x86::ID_REG_EIP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EIP, tmp);    break;
            case triton::arch::x86::ID_REG_EFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, tmp); break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0, tmp);   break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1, tmp);   break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2, tmp);   break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3, tmp);   break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4, tmp);   break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5, tmp);   break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6, tmp);   break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7, tmp);   break;
            default:
              if (reg.isFlag())
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, tmp);
              else
                throw std::runtime_error("tracer::pintool::getCurrentRegisterValue(): Invalid register.");
              break;
          }

        /* Sync with the libTriton */
        triton::arch::RegisterOperand syncReg;
        if (reg.isFlag())
          syncReg = TRITON_X86_REG_EFLAGS;
        else
          syncReg = reg.getParent();

        #endif

        syncReg.setConcreteValue(static_cast<triton::uint128>(*(reinterpret_cast<triton::uint128*>(tmp))));
        triton::api.setLastRegisterValue(syncReg);

        free(tmp);

        /* Returns the good casted value */
        return triton::api.getLastRegisterValue(reg);
      }


      triton::uint128 getCurrentMemoryValue(triton::arch::MemoryOperand& mem) {
        return tracer::pintool::context::getCurrentMemoryValue(mem.getAddress(), mem.getSize());
      }


      triton::uint128 getCurrentMemoryValue(triton::__uint addr) {
        if (PIN_CheckReadAccess(reinterpret_cast<void*>(addr)) == false)
          throw std::runtime_error("tracer::pintool::getCurrentMemoryValue(): Page not readable.");
        return static_cast<triton::uint128>(*(reinterpret_cast<triton::uint8*>(addr)));
      }


      triton::uint128 getCurrentMemoryValue(triton::__uint addr, triton::uint32 size) {
        if (PIN_CheckReadAccess(reinterpret_cast<void*>(addr)) == false || PIN_CheckReadAccess(reinterpret_cast<void*>(addr+size-1)) == false)
          throw std::runtime_error("tracer::pintool::getCurrentMemoryValue(): Page not readable.");

        switch(size) {
          case BYTE_SIZE:   return static_cast<triton::uint128>(*(reinterpret_cast<triton::uint8*>(addr)));
          case WORD_SIZE:   return static_cast<triton::uint128>(*(reinterpret_cast<triton::uint16*>(addr)));
          case DWORD_SIZE:  return static_cast<triton::uint128>(*(reinterpret_cast<triton::uint32*>(addr)));
          case QWORD_SIZE:  return static_cast<triton::uint128>(*(reinterpret_cast<triton::uint64*>(addr)));
          case DQWORD_SIZE: return static_cast<triton::uint128>(*(reinterpret_cast<triton::uint128*>(addr)));
        }
      }


      void setCurrentRegisterValue(triton::arch::RegisterOperand& reg) {
        tracer::pintool::context::setCurrentRegisterValue(reg, reg.getConcreteValue());
      }


      void setCurrentRegisterValue(triton::arch::RegisterOperand& reg, triton::uint128 value) {
        unsigned char *tmp = (unsigned char*)malloc(DQWORD_SIZE);
        *(reinterpret_cast<triton::uint128*>(tmp)) = value;

        if (reg.getId() != reg.getParent().getId() || reg.isFlag())
          throw std::runtime_error("tracer::pintool::setCurrentRegisterValue(): You cannot set a Pin register value on a sub-register or a flag.");

        #if defined(__x86_64__) || defined(_M_X64)
          switch (reg.getId()) {
            case triton::arch::x86::ID_REG_RAX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RAX, tmp);    break;
            case triton::arch::x86::ID_REG_RBX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBX, tmp);    break;
            case triton::arch::x86::ID_REG_RCX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RCX, tmp);    break;
            case triton::arch::x86::ID_REG_RDX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDX, tmp);    break;
            case triton::arch::x86::ID_REG_RDI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDI, tmp);    break;
            case triton::arch::x86::ID_REG_RSI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSI, tmp);    break;
            case triton::arch::x86::ID_REG_RBP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBP, tmp);    break;
            case triton::arch::x86::ID_REG_RSP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSP, tmp);    break;
            case triton::arch::x86::ID_REG_RIP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RIP, tmp);    break;
            case triton::arch::x86::ID_REG_RFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, tmp); break;
            case triton::arch::x86::ID_REG_R8:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8, tmp);     break;
            case triton::arch::x86::ID_REG_R9:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9, tmp);     break;
            case triton::arch::x86::ID_REG_R10:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10, tmp);    break;
            case triton::arch::x86::ID_REG_R11:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11, tmp);    break;
            case triton::arch::x86::ID_REG_R12:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12, tmp);    break;
            case triton::arch::x86::ID_REG_R13:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13, tmp);    break;
            case triton::arch::x86::ID_REG_R14:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14, tmp);    break;
            case triton::arch::x86::ID_REG_R15:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15, tmp);    break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0, tmp);   break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1, tmp);   break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2, tmp);   break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3, tmp);   break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4, tmp);   break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5, tmp);   break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6, tmp);   break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7, tmp);   break;
            case triton::arch::x86::ID_REG_XMM8:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM8, tmp);   break;
            case triton::arch::x86::ID_REG_XMM9:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM9, tmp);   break;
            case triton::arch::x86::ID_REG_XMM10:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM10, tmp);  break;
            case triton::arch::x86::ID_REG_XMM11:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM11, tmp);  break;
            case triton::arch::x86::ID_REG_XMM12:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM12, tmp);  break;
            case triton::arch::x86::ID_REG_XMM13:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM13, tmp);  break;
            case triton::arch::x86::ID_REG_XMM14:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM14, tmp);  break;
            case triton::arch::x86::ID_REG_XMM15:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM15, tmp);  break;
            default:
              throw std::runtime_error("tracer::pintool::setCurrentRegisterValue(): Invalid register.");
          }
        #endif

        #if defined(__i386) || defined(_M_IX86)
          switch (reg.getId()) {
            case triton::arch::x86::ID_REG_EAX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EAX, tmp);    break;
            case triton::arch::x86::ID_REG_EBX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBX, tmp);    break;
            case triton::arch::x86::ID_REG_ECX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ECX, tmp);    break;
            case triton::arch::x86::ID_REG_EDX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDX, tmp);    break;
            case triton::arch::x86::ID_REG_EDI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDI, tmp);    break;
            case triton::arch::x86::ID_REG_ESI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESI, tmp);    break;
            case triton::arch::x86::ID_REG_EBP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBP, tmp);    break;
            case triton::arch::x86::ID_REG_ESP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESP, tmp);    break;
            case triton::arch::x86::ID_REG_EIP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EIP, tmp);    break;
            case triton::arch::x86::ID_REG_EFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, tmp); break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0, tmp);   break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1, tmp);   break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2, tmp);   break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3, tmp);   break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4, tmp);   break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5, tmp);   break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6, tmp);   break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7, tmp);   break;
            default:
              throw std::runtime_error("tracer::pintool::setCurrentRegisterValue(): Invalid register.");
          }
        #endif

        /* Sync with the libTriton */
        triton::arch::RegisterOperand syncReg(reg);
        syncReg.setConcreteValue(value);
        triton::api.setLastRegisterValue(syncReg);

        /* We must concretize the register because the last symbolic value is now false */
        triton::api.concretizeReg(reg);

        /* Define that the context must be executed as soon as possible */
        tracer::pintool::context::mustBeExecuted = true;

        free(tmp);
      }


      void setCurrentMemoryValue(triton::arch::MemoryOperand& mem) {
        tracer::pintool::context::setCurrentMemoryValue(mem, mem.getConcreteValue());
      }


      void setCurrentMemoryValue(triton::arch::MemoryOperand& mem, triton::uint128 value) {
        triton::__uint  addr  = mem.getAddress();
        triton::uint32  size  = mem.getSize();

        /* Sync with the libTriton */
        mem.setConcreteValue(value);
        triton::api.setLastMemoryValue(mem);

        /* We must concretize the memory because the last symbolic value is now false */
        triton::api.concretizeMem(mem);

        /* Inject memory value */
        for (triton::uint32 i = 0; i <= size; i++) {
          if (PIN_CheckWriteAccess(reinterpret_cast<void*>((addr+i))) == false)
            throw std::runtime_error("tracer::pintool::setCurrentMemoryValue(): Page not writable.");
          *((triton::uint8 *)(addr+i)) = static_cast<triton::uint8>(value & 0xff);
          value >>= 8;
        }
      }


      void setCurrentMemoryValue(triton::__uint addr, triton::uint8 value) {
        if (PIN_CheckWriteAccess(reinterpret_cast<void*>(addr)) == false)
          throw std::runtime_error("tracer::pintool::setCurrentMemoryValue(): Page not writable.");

        /* Sync with the libTriton */
        triton::api.setLastMemoryValue(addr, value);

        /* We must concretize the memory because the last symbolic value is now false */
        triton::api.concretizeMem(addr);

        /* Inject memory value */
        *((triton::uint8*)(addr)) = static_cast<triton::uint8>(value & 0xff);
      }


      void executeContext(void) {
        if (tracer::pintool::context::mustBeExecuted == true) {
          PIN_UnlockClient();
          PIN_ExecuteAt(tracer::pintool::context::lastContext);
        }
      }

    };
  };
};
