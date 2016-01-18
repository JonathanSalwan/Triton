//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

/* libTriton */
#include <api.hpp>
#include <x86Specifications.hpp>

/* pintool */
#include "utils.hpp"



namespace tracer {
  namespace pintool {

    triton::__uint getBaseAddress(triton::__uint address) {
      RTN rtn;
      SEC sec;
      IMG img;
      PIN_LockClient();
      rtn = RTN_FindByAddress(address);
      PIN_UnlockClient();
      if (RTN_Valid(rtn)) {
        sec = RTN_Sec(rtn);
        if (SEC_Valid(sec)) {
          img = SEC_Img(sec);
          if (IMG_Valid(img)) {
            return IMG_LowAddress(img);
          }
        }
      }
      return 0;
    }


    std::string getImageName(triton::__uint address) {
      RTN rtn;
      SEC sec;
      IMG img;
      PIN_LockClient();
      rtn = RTN_FindByAddress(address);
      PIN_UnlockClient();
      if (RTN_Valid(rtn)) {
        sec = RTN_Sec(rtn);
        if (SEC_Valid(sec)) {
          img = SEC_Img(sec);
          if (IMG_Valid(img)) {
            return IMG_Name(img);
          }
        }
      }
      return "";
    }


    triton::__uint getInsOffset(triton::__uint address) {
      triton::__uint base = tracer::pintool::getBaseAddress(address);
      if (base == 0)
        return 0;
      return address - base;
    }


    void setupContextRegister(triton::arch::Instruction* inst, CONTEXT* ctx) {
      triton::uint64 value = 0;

      #if defined(__x86_64__) || defined(_M_X64)
        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RAX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RAX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RBX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RBX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RCX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RCX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RDX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RDX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RDI, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RDI, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RSI, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSI, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RBP, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RBP, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RSP, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RSP, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RIP, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RIP, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_RFLAGS, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R8, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R8, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R9, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R9, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R10, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R10, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R11, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R11, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R12, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R12, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R13, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R13, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R14, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R14, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_R15, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_R15, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM0, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM1, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM2, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM3, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM4, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM5, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM6, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM7, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM8, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM8, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM9, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM9, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM10, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM10, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM11, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM11, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM12, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM12, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM13, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM13, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM14, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM14, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM15, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM15, value));
      #endif

      #if defined(__i386) || defined(_M_IX86)
        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EAX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EAX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EBX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_ECX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ECX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EDX, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDX, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EDI, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EDI, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_ESI, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESI, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EBP, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EBP, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_ESP, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_ESP, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EIP, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EIP, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_EFLAGS, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM0, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM0, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM1, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM1, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM2, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM2, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM3, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM3, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM4, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM4, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM5, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM5, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM6, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM6, value));

        PIN_GetContextRegval(ctx, LEVEL_BASE::REG_XMM7, reinterpret_cast<triton::uint8 *>(&value));
        inst->updateContext(triton::arch::RegisterOperand(triton::arch::x86::ID_REG_XMM7, value));
      #endif
    }

  };
};

