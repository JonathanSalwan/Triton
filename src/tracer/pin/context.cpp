//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <cstring>
#include <stdexcept>

/* libTriton */
#include <cpuSize.hpp>
#include <coreUtils.hpp>
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
        triton::uint8 buffer[DQWORD_SIZE] = {0};
        triton::uint128 value = 0;

        #if defined(__x86_64__) || defined(_M_X64)
          switch (reg.getParent().getId()) {
            case triton::arch::x86::ID_REG_RAX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RBX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RCX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RCX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RDX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RDI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RSI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RBP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RSP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RIP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R8:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R9:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R10:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R11:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R12:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R13:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R14:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R15:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM8:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM9:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM10:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM11:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM12:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM13:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM14:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM15:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              if (reg.isFlag())
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer));
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
            case triton::arch::x86::ID_REG_EAX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EBX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ECX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ECX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EDX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EDI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ESI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EBP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ESP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EIP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              if (reg.isFlag())
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer));
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

        value = triton::fromBufferToUint128(buffer);
        syncReg.setConcreteValue(value);
        triton::api.setLastRegisterValue(syncReg);

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
        triton::uint128 value = 0;

        if (PIN_CheckReadAccess(reinterpret_cast<void*>(addr)) == false || PIN_CheckReadAccess(reinterpret_cast<void*>(addr+size-1)) == false)
          throw std::runtime_error("tracer::pintool::getCurrentMemoryValue(): Page not readable.");

        switch(size) {
          case BYTE_SIZE:   value = *(reinterpret_cast<triton::uint8*>(addr));                            break;
          case WORD_SIZE:   value = *(reinterpret_cast<triton::uint16*>(addr));                           break;
          case DWORD_SIZE:  value = *(reinterpret_cast<triton::uint32*>(addr));                           break;
          case QWORD_SIZE:  value = *(reinterpret_cast<triton::uint64*>(addr));                           break;
          case DQWORD_SIZE: value = triton::fromBufferToUint128(reinterpret_cast<triton::uint8*>(addr));  break;
        }

        return value;
      }


      void setCurrentRegisterValue(triton::arch::RegisterOperand& reg) {
        tracer::pintool::context::setCurrentRegisterValue(reg, reg.getConcreteValue());
      }


      void setCurrentRegisterValue(triton::arch::RegisterOperand& reg, triton::uint128 value) {
        triton::uint8 buffer[DQWORD_SIZE] = {0};

        if (reg.getId() != reg.getParent().getId() || reg.isFlag())
          throw std::runtime_error("tracer::pintool::setCurrentRegisterValue(): You cannot set a Pin register value on a sub-register or a flag.");

        triton::fromUint128ToBuffer(value, buffer);

        #if defined(__x86_64__) || defined(_M_X64)
          switch (reg.getId()) {
            case triton::arch::x86::ID_REG_RAX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RBX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RCX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RCX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RDX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RDI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RSI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RBP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RSP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RIP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_RFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R8:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R9:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R10:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R11:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R12:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R13:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R14:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R15:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM8:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM9:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM10:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM11:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM12:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM13:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM14:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM15:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              throw std::runtime_error("tracer::pintool::setCurrentRegisterValue(): Invalid register.");
          }
        #endif

        #if defined(__i386) || defined(_M_IX86)
          switch (reg.getId()) {
            case triton::arch::x86::ID_REG_EAX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EBX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ECX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ECX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EDX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EDI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ESI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EBP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ESP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EIP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_EFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
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


      void setupContextRegister(triton::arch::Instruction* inst, CONTEXT* ctx) {
        triton::uint8 buffer[DQWORD_SIZE] = {0};

        #if defined(__x86_64__) || defined(_M_X64)
          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RAX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RAX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RBX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RBX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RCX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RCX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RDX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RDX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RDI, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RDI, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RSI, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSI, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RBP, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RBP, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RSP, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSP, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RIP, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RIP, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RFLAGS, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R8, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R8, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R9, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R9, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R10, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R10, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R11, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R11, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R12, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R12, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R13, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R13, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R14, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R14, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R15, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R15, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM0, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM1, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM2, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM3, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM4, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM5, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM6, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM7, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM8, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM8, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM9, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM9, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM10, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM10, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM11, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM11, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM12, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM12, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM13, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM13, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM14, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM14, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM15, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM15, triton::fromBufferToUint128(buffer)));
        #endif

        #if defined(__i386) || defined(_M_IX86)
          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EAX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EAX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EBX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_ECX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ECX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EDX, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDX, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EDI, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDI, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_ESI, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESI, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EBP, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBP, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_ESP, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESP, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EIP, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EIP, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EFLAGS, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM0, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM1, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM2, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM3, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM4, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM5, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM6, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6, triton::fromBufferToUint128(buffer)));

          PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM7, reinterpret_cast<triton::uint8 *>(buffer));
          inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7, triton::fromBufferToUint128(buffer)));
        #endif
      }

    };
  };
};
