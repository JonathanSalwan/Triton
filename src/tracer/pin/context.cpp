//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>
#include <stdexcept>

/* libTriton */
#include <triton/cpuSize.hpp>
#include <triton/coreUtils.hpp>
#include <triton/x86Specifications.hpp>

/* pintool */
#include "bindings.hpp"
#include "context.hpp"



namespace tracer {
  namespace pintool {
    namespace context {

      CONTEXT* lastContext    = nullptr;
      bool     mustBeExecuted = false;


      triton::uint512 getCurrentRegisterValue(const triton::arch::Register& reg) {
        triton::uint8 buffer[DQQWORD_SIZE] = {0};
        triton::uint512 value = 0;

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
            case triton::arch::x86::ID_REG_EFLAGS:  PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R8:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R8,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R9:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R9,     reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R10:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R10,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R11:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R11,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R12:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R12,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R13:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R13,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R14:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R14,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_R15:     PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_R15,    reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_MM0:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM1:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM2:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM3:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM4:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM5:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM6:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM7:     return 0; /* Pin doesn't support MMX */
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
            case triton::arch::x86::ID_REG_YMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM8:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM9:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM10:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM11:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM12:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM13:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM14:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM15:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ZMM0:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM1:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM2:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM3:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM4:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM5:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM6:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM7:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM8:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM9:    return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM10:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM11:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM12:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM13:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM14:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM15:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM16:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM17:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM18:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM19:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM20:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM21:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM22:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM23:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM24:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM25:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM26:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM27:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM28:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM29:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM30:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_ZMM31:   return 0; /* Pin doesn't support AVX-512 */
            case triton::arch::x86::ID_REG_MXCSR:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_CR0:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR1:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR2:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR3:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR4:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR5:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR6:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR7:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR8:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR9:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR10:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR11:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR12:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR13:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR14:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR15:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_DS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ES:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_FS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_GS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_SS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              if (reg.getId() >= triton::arch::x86::ID_REG_AF && reg.getId() <= triton::arch::x86::ID_REG_ZF)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer));
              else if (reg.getId() >= triton::arch::x86::ID_REG_IE && reg.getId() <= triton::arch::x86::ID_REG_FZ)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR, reinterpret_cast<triton::uint8*>(buffer));
              else
                throw std::runtime_error("tracer::pintool::context::getCurrentRegisterValue(): Invalid register.");
              break;
          }

        /* Sync with the libTriton */
        triton::arch::Register syncReg;
        if (reg.getId() >= triton::arch::x86::ID_REG_AF && reg.getId() <= triton::arch::x86::ID_REG_ZF)
          syncReg = TRITON_X86_REG_EFLAGS;
        else if (reg.getId() >= triton::arch::x86::ID_REG_IE && reg.getId() <= triton::arch::x86::ID_REG_FZ)
          syncReg = TRITON_X86_REG_MXCSR;
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
            case triton::arch::x86::ID_REG_MM0:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM1:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM2:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM3:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM4:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM5:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM6:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_MM7:     return 0; /* Pin doesn't support MMX */
            case triton::arch::x86::ID_REG_XMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_XMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_XMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM0:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM1:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM2:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM3:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM4:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM5:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM6:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM7:    PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_MXCSR:   PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_CR0:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR1:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR2:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR3:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR4:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR5:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR6:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR7:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR8:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR9:     return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR10:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR11:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR12:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR13:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR14:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CR15:    return 0; /* Don't care about this register in ring3 */
            case triton::arch::x86::ID_REG_CS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_DS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ES:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES,       reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_FS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_GS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS_BASE,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_SS:      PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS,       reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              if (reg.getId() >= triton::arch::x86::ID_REG_AF && reg.getId() <= triton::arch::x86::ID_REG_ZF)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_EFLAGS, reinterpret_cast<triton::uint8*>(buffer));
              else if (reg.getId() >= triton::arch::x86::ID_REG_IE && reg.getId() <= triton::arch::x86::ID_REG_FZ)
                PIN_GetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR, reinterpret_cast<triton::uint8*>(buffer));
              else
                throw std::runtime_error("tracer::pintool::context::getCurrentRegisterValue(): Invalid register.");
              break;
          }

        /* Sync with the libTriton */
        triton::arch::Register syncReg;
        if (reg.getId() >= triton::arch::x86::ID_REG_AF && reg.getId() <= triton::arch::x86::ID_REG_ZF)
          syncReg = TRITON_X86_REG_EFLAGS;
        else if (reg.getId() >= triton::arch::x86::ID_REG_IE && reg.getId() <= triton::arch::x86::ID_REG_FZ)
          syncReg = TRITON_X86_REG_MXCSR;
        else
          syncReg = reg.getParent();
        #endif

        value = triton::utils::fromBufferToUint<triton::uint512>(buffer);
        syncReg.setConcreteValue(value);
        triton::api.setConcreteRegisterValue(syncReg);

        /* Returns the good casted value */
        return triton::api.getConcreteRegisterValue(reg, false);
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
          case BYTE_SIZE:    value = *(reinterpret_cast<triton::uint8*>(addr));  break;
          case WORD_SIZE:    value = *(reinterpret_cast<triton::uint16*>(addr)); break;
          case DWORD_SIZE:   value = *(reinterpret_cast<triton::uint32*>(addr)); break;
          case QWORD_SIZE:   value = *(reinterpret_cast<triton::uint64*>(addr)); break;
          case DQWORD_SIZE:  value = triton::utils::fromBufferToUint<triton::uint128>(reinterpret_cast<triton::uint8*>(addr)); break;
          case QQWORD_SIZE:  value = triton::utils::fromBufferToUint<triton::uint256>(reinterpret_cast<triton::uint8*>(addr)); break;
          case DQQWORD_SIZE: value = triton::utils::fromBufferToUint<triton::uint512>(reinterpret_cast<triton::uint8*>(addr)); break;
        }

        return value;
      }


      void setCurrentRegisterValue(triton::arch::Register& reg) {
        tracer::pintool::context::setCurrentRegisterValue(reg, reg.getConcreteValue());
      }


      void setCurrentRegisterValue(triton::arch::Register& reg, triton::uint512 value) {
        triton::uint8 buffer[DQQWORD_SIZE] = {0};

        if (reg.getId() != reg.getParent().getId() || triton::api.isFlag(reg))
          throw std::runtime_error("tracer::pintool::context::setCurrentRegisterValue(): You cannot set a Pin register value on a sub-register or a flag.");

        triton::utils::fromUintToBuffer(value, buffer);

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
            case triton::arch::x86::ID_REG_EFLAGS:  PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_RFLAGS, reinterpret_cast<triton::uint8*>(buffer)); break;
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
            case triton::arch::x86::ID_REG_YMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM8:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM8,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM9:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM9,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM10:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM10,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM11:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM11,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM12:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM12,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM13:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM13,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM14:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM14,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM15:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM15,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_MXCSR:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_CS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_DS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ES:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_FS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_GS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_SS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS, reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              throw std::runtime_error("tracer::pintool::context::setCurrentRegisterValue(): Invalid register.");
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
            case triton::arch::x86::ID_REG_YMM0:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM0,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM1:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM1,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM2:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM2,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM3:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM3,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM4:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM4,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM5:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM5,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM6:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM6,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_YMM7:    PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_YMM7,   reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_MXCSR:   PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_MXCSR,  reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_CS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_CS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_DS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_DS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_ES:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_ES, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_FS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_FS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_GS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_GS, reinterpret_cast<triton::uint8*>(buffer)); break;
            case triton::arch::x86::ID_REG_SS:      PIN_SetContextRegval(tracer::pintool::context::lastContext, LEVEL_BASE::REG_SEG_SS, reinterpret_cast<triton::uint8*>(buffer)); break;
            default:
              throw std::runtime_error("tracer::pintool::context::setCurrentRegisterValue(): Invalid register.");
          }
        #endif

        /* Sync with the libTriton */
        triton::arch::Register syncReg(reg);
        syncReg.setConcreteValue(value);
        triton::api.setConcreteRegisterValue(syncReg);

        /* We must concretize the register because the last symbolic value is now false */
        triton::api.concretizeRegister(reg);

        /* Define that the context must be executed as soon as possible */
        tracer::pintool::context::mustBeExecuted = true;
      }


      void setCurrentMemoryValue(triton::arch::MemoryAccess& mem) {
        tracer::pintool::context::setCurrentMemoryValue(mem, mem.getConcreteValue());
      }


      void setCurrentMemoryValue(triton::arch::MemoryAccess& mem, triton::uint512 value) {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        /* Sync with the libTriton */
        mem.setConcreteValue(value);
        triton::api.setConcreteMemoryValue(mem);

        /* We must concretize the memory because the last symbolic value is now false */
        triton::api.concretizeMemory(mem);

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
        triton::api.setConcreteMemoryValue(addr, value);

        /* We must concretize the memory because the last symbolic value is now false */
        triton::api.concretizeMemory(addr);

        /* Inject memory value */
        *((triton::uint8*)(addr)) = (value & 0xff);
      }


      void executeContext(void) {
        if (tracer::pintool::context::mustBeExecuted == true) {
          PIN_UnlockClient();
          PIN_ExecuteAt(tracer::pintool::context::lastContext);
        }
      }


      void needConcreteRegisterValue(triton::arch::Register& reg) {
        triton::uint512 value = tracer::pintool::context::getCurrentRegisterValue(reg);
        triton::arch::Register tmp(reg.getId(), value);
        triton::api.setConcreteRegisterValue(tmp);
      }


      void synchronizeContext(void) {
        if (triton::api.isSymbolicEngineEnabled() == false)
          return;

        for (triton::arch::Register* reg : triton::api.getParentRegisters()) {
          if (reg->getId() > triton::arch::x86::ID_REG_EFLAGS)
            continue;

          if (triton::api.getSymbolicRegisterId(*reg) == triton::engines::symbolic::UNSET)
            continue;

          triton::uint512 cv = tracer::pintool::context::getCurrentRegisterValue(*reg);
          triton::uint512 sv = triton::api.getSymbolicRegisterValue(*reg);

          if (sv != cv) {
            triton::api.concretizeRegister(*reg);
            triton::api.setConcreteRegisterValue(triton::arch::Register(reg->getId(), cv));
          }
        }
      }

    };
  };
};
