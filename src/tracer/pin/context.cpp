//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

/* pintool */
#include "bindings.hpp"
#include "api.hpp"
#include "context.hpp"

#include <cstring>
#include <stdexcept>

/* libTriton */
#include <triton/api.hpp>
#include <triton/cpuSize.hpp>
#include <triton/coreUtils.hpp>
#include <triton/x86Specifications.hpp>




namespace tracer {
  namespace pintool {
    namespace context {

      CONTEXT* lastContext    = nullptr;
      bool     mustBeExecuted = false;


      triton::uint512 getCurrentRegisterValue(const triton::arch::Register& reg) {
        triton::uint8 buffer[triton::size::dqqword] = {0};
        triton::uint512 value = 0;

        if (tracer::pintool::context::lastContext == nullptr)
          return 0;

        #if defined(__x86_64__) || defined(_M_X64)
          switch (reg.getParent()) {
            case triton::arch::ID_REG_X86_RAX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RBX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RCX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RCX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RDX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RDI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RSI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RBP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RSP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RIP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R8:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R9:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R10:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R11:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R12:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R13:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R14:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R15:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_MM0:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM1:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM2:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM3:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM4:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM5:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM6:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM7:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM8:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM9:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM10:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM11:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM12:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM13:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM14:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM15:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM8:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM9:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM10:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM11:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM12:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM13:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM14:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM15:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM8:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM9:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM10:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM11:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM12:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM13:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM14:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM15:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ZMM16:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM17:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM18:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM19:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM20:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM21:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM22:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM23:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM24:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM25:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM26:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM27:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM28:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM29:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM30:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_ZMM31:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::ID_REG_X86_MXCSR:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_CR0:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR1:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR2:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR3:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR4:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR5:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR6:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR7:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR8:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR9:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR10:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR11:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR12:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR13:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR14:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR15:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_DS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ES:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_FS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_GS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_SS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              if (reg.getId() >= triton::arch::ID_REG_X86_AC && reg.getId() <= triton::arch::ID_REG_X86_ZF)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer));
              else if (reg.getId() >= triton::arch::ID_REG_X86_IE && reg.getId() <= triton::arch::ID_REG_X86_FZ)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR, reinterpret_cast<triton::uint8*>(buffer));
              else
                throw std::runtime_error("tracer::pintool::context::getCurrentRegisterValue(): Invalid register.");
              break;
          }

        /* Sync with the libTriton */
        const triton::arch::Register* syncReg = nullptr;
        if (reg.getId() >= triton::arch::ID_REG_X86_AC && reg.getId() <= triton::arch::ID_REG_X86_ZF)
          syncReg = &tracer::pintool::api.getRegister(triton::arch::ID_REG_X86_EFLAGS);
        else if (reg.getId() >= triton::arch::ID_REG_X86_IE && reg.getId() <= triton::arch::ID_REG_X86_FZ)
          syncReg = &tracer::pintool::api.getRegister(triton::arch::ID_REG_X86_MXCSR);
        else
          syncReg = &tracer::pintool::api.getParentRegister(reg.getId());
        #endif

        #if defined(__i386) || defined(_M_IX86)
          switch (reg.getParent()) {
            case triton::arch::ID_REG_X86_EAX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EBX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ECX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ECX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EDX:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EDI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ESI:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EBP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ESP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EIP:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_MM0:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM1:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM2:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM3:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM4:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM5:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM6:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_MM7:     return 0; /* Pin doesn't support MMX */
            case triton::arch::ID_REG_X86_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_MXCSR:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_CR0:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR1:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR2:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR3:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR4:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR5:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR6:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR7:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR8:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR9:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR10:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR11:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR12:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR13:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR14:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CR15:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::ID_REG_X86_CS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_DS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ES:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_FS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_GS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_SS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              if (reg.getId() >= triton::arch::ID_REG_X86_AC && reg.getId() <= triton::arch::ID_REG_X86_ZF)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer));
              else if (reg.getId() >= triton::arch::ID_REG_X86_IE && reg.getId() <= triton::arch::ID_REG_X86_FZ)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR, reinterpret_cast<triton::uint8*>(buffer));
              else
                throw std::runtime_error("tracer::pintool::context::getCurrentRegisterValue(): Invalid register.");
              break;
          }

        /* Sync with the libTriton */
        const triton::arch::Register* syncReg = nullptr;
        if (reg.getId() >= triton::arch::ID_REG_X86_AC && reg.getId() <= triton::arch::ID_REG_X86_ZF)
          syncReg = &tracer::pintool::api.getRegister(triton::arch::ID_REG_X86_EFLAGS);
        else if (reg.getId() >= triton::arch::ID_REG_X86_IE && reg.getId() <= triton::arch::ID_REG_X86_FZ)
          syncReg = &tracer::pintool::api.getRegister(triton::arch::ID_REG_X86_MXCSR);
        else
          syncReg = &tracer::pintool::api.getParentRegister(reg.getId());
        #endif

        value = triton::utils::fromBufferToUint<triton::uint512>(buffer);
        tracer::pintool::api.getCpuInstance()->setConcreteRegisterValue(*syncReg, value);

        /* Returns the good casted value */
        return tracer::pintool::api.getConcreteRegisterValue(reg, false);
      }


      triton::uint512 getCurrentMemoryValue(const triton::arch::MemoryAccess& mem) {
        return tracer::pintool::context::getCurrentMemoryValue(mem.getAddress(), mem.getSize());
      }


      triton::uint512 getCurrentMemoryValue(triton::__uint addr) {
        triton::uint512 value = 0;

        if (PIN_CheckReadAccess(reinterpret_cast<triton::uint8*>(addr)) == false)
          throw std::runtime_error("tracer::pintool::context::getCurrentMemoryValue(): Page not readable.");

        value = *(reinterpret_cast<triton::uint8*>(addr));

        return value;
      }


      triton::uint512 getCurrentMemoryValue(triton::__uint addr, triton::uint32 size) {
        triton::uint512 value = 0;

        if (PIN_CheckReadAccess(reinterpret_cast<triton::uint8*>(addr)) == false || PIN_CheckReadAccess(reinterpret_cast<triton::uint8*>(addr+size-1)) == false)
          throw std::runtime_error("tracer::pintool::context::getCurrentMemoryValue(): Page not readable.");

        switch(size) {
          case triton::size::byte:    value = *(reinterpret_cast<triton::uint8*>(addr));  break;
          case triton::size::word:    value = *(reinterpret_cast<triton::uint16*>(addr)); break;
          case triton::size::dword:   value = *(reinterpret_cast<triton::uint32*>(addr)); break;
          case triton::size::qword:   value = *(reinterpret_cast<triton::uint64*>(addr)); break;
          case triton::size::dqword:  value = triton::utils::fromBufferToUint<triton::uint128>(reinterpret_cast<triton::uint8*>(addr)); break;
          case triton::size::qqword:  value = triton::utils::fromBufferToUint<triton::uint256>(reinterpret_cast<triton::uint8*>(addr)); break;
          case triton::size::dqqword: value = triton::utils::fromBufferToUint<triton::uint512>(reinterpret_cast<triton::uint8*>(addr)); break;
        }

        return value;
      }


      void setCurrentRegisterValue(const triton::arch::Register& reg, triton::uint512 value) {
        triton::uint8 buffer[triton::size::dqqword] = {0};

        if (reg.getId() != reg.getParent() || tracer::pintool::api.isFlag(reg))
          throw std::runtime_error("tracer::pintool::context::setCurrentRegisterValue(): You cannot set a Pin register value on a sub-register or a flag.");

        if (tracer::pintool::context::lastContext == nullptr)
          return;

        triton::utils::fromUintToBuffer(value, buffer);

        #if defined(__x86_64__) || defined(_M_X64)
          switch (reg.getId()) {
            case triton::arch::ID_REG_X86_RAX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RBX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RCX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RCX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RDX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RDI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RSI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RBP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RSP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RSP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_RIP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R8:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R9:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R10:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R11:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R12:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R13:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R14:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_R15:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM8:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM9:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM10:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM11:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM12:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM13:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM14:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM15:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM8:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM9:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM10:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM11:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM12:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM13:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM14:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM15:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_MXCSR:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_CS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_DS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ES:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_FS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_GS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_SS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS, reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              throw std::runtime_error("tracer::pintool::context::setCurrentRegisterValue(): Invalid register.");
          }
        #endif

        #if defined(__i386) || defined(_M_IX86)
          switch (reg.getId()) {
            case triton::arch::ID_REG_X86_EAX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EAX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EBX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ECX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ECX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EDX:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDX,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EDI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EDI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ESI:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESI,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EBP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EBP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ESP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_ESP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EIP:     PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EIP,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_EFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_XMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_YMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_MXCSR:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_CS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_DS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_ES:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_FS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_GS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::ID_REG_X86_SS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS, reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              throw std::runtime_error("tracer::pintool::context::setCurrentRegisterValue(): Invalid register.");
          }
        #endif

        /* Sync with the libTriton */
        const triton::arch::Register syncReg(reg);
        tracer::pintool::api.setConcreteRegisterValue(syncReg, value);

        /* Define that the context must be executed as soon as possible */
        tracer::pintool::context::mustBeExecuted = true;
      }


      void setCurrentMemoryValue(const triton::arch::MemoryAccess& mem, triton::uint512 value) {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        /* Sync with the libTriton */
        tracer::pintool::api.setConcreteMemoryValue(mem, value);

        /* Inject memory value */
        for (triton::uint32 i = 0; i < size; i++) {
          if (PIN_CheckWriteAccess(reinterpret_cast<triton::uint8*>((addr+i))) == false)
            throw std::runtime_error("tracer::pintool::context::setCurrentMemoryValue(): Page not writable.");
          *((triton::uint8 *)(addr+i)) = (value & 0xff).convert_to<triton::uint8>();
          value >>= 8;
        }
      }


      void setCurrentMemoryValue(triton::__uint addr, triton::uint8 value) {
        if (PIN_CheckWriteAccess(reinterpret_cast<triton::uint8*>(addr)) == false)
          throw std::runtime_error("tracer::pintool::context::setCurrentMemoryValue(): Page not writable.");

        /* Sync with the libTriton */
        tracer::pintool::api.setConcreteMemoryValue(addr, value);

        /* Inject memory value */
        *((triton::uint8*)(addr)) = (value & 0xff);
      }


      void executeContext(void) {
        if (tracer::pintool::context::mustBeExecuted == true) {
          PIN_UnlockClient();
          PIN_ExecuteAt(tracer::pintool::context::lastContext);
        }
      }


      void needConcreteMemoryValue(triton::API& api, const triton::arch::MemoryAccess& mem) {
        triton::uint512 cv = tracer::pintool::context::getCurrentMemoryValue(mem);
        tracer::pintool::api.getCpuInstance()->setConcreteMemoryValue(mem, cv);
      }


      void synchronizeContext(void) {
        if (tracer::pintool::api.isSymbolicEngineEnabled() == false)
          return;

        for (const triton::arch::Register* reg : tracer::pintool::api.getParentRegisters()) {
          triton::arch::register_e regId = reg->getId();

          if (regId > triton::arch::ID_REG_X86_EFLAGS && !(regId >= triton::arch::ID_REG_X86_CS && regId <= triton::arch::ID_REG_X86_SS))
            continue;

          triton::uint512 cv = tracer::pintool::context::getCurrentRegisterValue(triton::arch::Register(*reg));
          triton::uint512 sv = tracer::pintool::api.getSymbolicRegisterValue(triton::arch::Register(*reg));

          if (sv != cv) {
            tracer::pintool::api.setConcreteRegisterValue(*reg, cv);
          }
        }
      }

    };
  };
};
