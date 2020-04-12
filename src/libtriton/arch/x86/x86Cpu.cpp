//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <triton/architecture.hpp>
#include <triton/coreUtils.hpp>
#include <triton/cpuSize.hpp>
#include <triton/exceptions.hpp>
#include <triton/immediate.hpp>
#include <triton/x86Cpu.hpp>

// Read macros

#define GRP_READ_2(name, reg) {                                         \
  case triton::arch::ID_REG_X86_E ## name ## X: {                       \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint32*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## X: {                        \
    triton::uint16 val = 0;                                             \
    std::memcpy(&val, (triton::uint16*)this->reg, triton::size::word);  \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## H: {                        \
    triton::uint8 val = 0;                                              \
    std::memcpy(&val, (triton::uint8*)this->reg+1, triton::size::byte); \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## L: {                        \
    triton::uint8 val = 0;                                              \
    std::memcpy(&val, (triton::uint8*)this->reg, triton::size::byte);   \
    return val;                                                         \
  }                                                                     \
}

#define GRP_READ_3(name, reg) {                                         \
  case triton::arch::ID_REG_X86_E ## name: {                            \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint32*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    triton::uint16 val = 0;                                             \
    std::memcpy(&val, (triton::uint16*)this->reg, triton::size::word);  \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## L: {                        \
    triton::uint8 val = 0;                                              \
    std::memcpy(&val, (triton::uint8*)this->reg, triton::size::byte);   \
    return val;                                                         \
  }                                                                     \
}

#define GRP_READ_4(name, reg) {                                         \
  case triton::arch::ID_REG_X86_E ## name: {                            \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint32*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    triton::uint16 val = 0;                                             \
    std::memcpy(&val, (triton::uint16*)this->reg, triton::size::word);  \
    return val;                                                         \
  }                                                                     \
}

#define CRR_READ(index, reg) {                                          \
  case triton::arch::ID_REG_X86_CR ## index: {                          \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
}

#define DRR_READ(index, reg) {                                          \
  case triton::arch::ID_REG_X86_DR ## index: {                          \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint32*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
}

#define SEG_READ(name, reg) {                                           \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint32*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
}

#define MMX_READ(index, reg) {                                          \
  case triton::arch::ID_REG_X86_MM ## index: {                          \
    triton::uint80 val = 0;                                             \
    std::memcpy(&val, (triton::uint80*)this->reg, triton::size::fword); \
    return val;                                                         \
  }                                                                     \
}

#define XMM_READ(index, reg) {                                            \
  case triton::arch::ID_REG_X86_XMM ## index: {                           \
    triton::uint128 val = 0;                                              \
    std::memcpy(&val, (triton::uint128*)this->reg, triton::size::dqword); \
    return val;                                                           \
  }                                                                       \
}

#define YMM_READ(index, reg) {                                            \
  case triton::arch::ID_REG_X86_YMM ## index: {                           \
    triton::uint256 val = 0;                                              \
    std::memcpy(&val, (triton::uint256*)this->reg, triton::size::qqword); \
    return val;                                                           \
  }                                                                       \
}

#define GR_READ(name, reg, size) {                                      \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    triton::size val = 0;                                               \
    std::memcpy(&val, (triton::size*)this->reg, sizeof(triton::size));  \
    return val;                                                         \
  }                                                                     \
}

#define FLG_READ(name, reg, size, off) {                                  \
  case triton::arch::ID_REG_X86_ ## name: {                               \
    triton::size flag = 0;                                                \
    std::memcpy(&flag, (triton::size*)this->reg, sizeof(triton::size));   \
    return ((flag >> off) & 1);                                           \
  }                                                                       \
}

// Write macros

#define GRP_WRITE_2(name, reg) {                                          \
  case triton::arch::ID_REG_X86_E ## name ## X: {                         \
    auto val = value.convert_to<triton::uint32>();                        \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword);   \
  } break;                                                                \
  case triton::arch::ID_REG_X86_ ## name ## X: {                          \
    auto val = value.convert_to<triton::uint16>();                        \
    std::memcpy((triton::uint16*)this->reg, &val, triton::size::word);    \
  } break;                                                                \
  case triton::arch::ID_REG_X86_ ## name ## H: {                          \
    auto val = value.convert_to<triton::uint8>();                         \
    std::memcpy((triton::uint8*)(this->reg+1), &val, triton::size::byte); \
  } break;                                                                \
  case triton::arch::ID_REG_X86_ ## name ## L: {                          \
    auto val = value.convert_to<triton::uint8>();                         \
    std::memcpy((triton::uint8*)this->reg, &val, triton::size::byte);     \
  } break;                                                                \
}

#define GRP_WRITE_3(name, reg) {                                        \
  case triton::arch::ID_REG_X86_E ## name: {                            \
    auto val = value.convert_to<triton::uint32>();                      \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword); \
  } break;                                                              \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    auto val = value.convert_to<triton::uint16>();                      \
    std::memcpy((triton::uint16*)this->reg, &val, triton::size::word);  \
  } break;                                                              \
  case triton::arch::ID_REG_X86_ ## name ## L: {                        \
    auto val = value.convert_to<triton::uint8>();                       \
    std::memcpy((triton::uint8*)this->reg, &val, triton::size::byte);   \
  } break;                                                              \
}

#define GRP_WRITE_4(name, reg) {                                        \
  case triton::arch::ID_REG_X86_E ## name: {                            \
    auto val = value.convert_to<triton::uint32>();                      \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword); \
  } break;                                                              \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    auto val = value.convert_to<triton::uint16>();                      \
    std::memcpy((triton::uint16*)this->reg, &val, triton::size::word);  \
  } break;                                                              \
}

#define CRR_WRITE(index, reg) {                                         \
  case triton::arch::ID_REG_X86_CR ## index: {                          \
    auto val = value.convert_to<triton::uint32>();                      \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword); \
  } break;                                                              \
}

#define DRR_WRITE(index, reg) {                                         \
  case triton::arch::ID_REG_X86_DR ## index: {                          \
    auto val = value.convert_to<triton::uint32>();                      \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword); \
  } break;                                                              \
}

#define SEG_WRITE(name, reg) {                                          \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    auto val = value.convert_to<triton::uint32>();                      \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword); \
  } break;                                                              \
}

#define MMX_WRITE(index, reg) {                                         \
  case triton::arch::ID_REG_X86_MM ## index: {                          \
    auto val = value.convert_to<triton::uint80>();                      \
    std::memcpy((triton::uint80*)this->reg, &val, triton::size::fword); \
  } break;                                                              \
}

#define XMM_WRITE(index, reg) {                                           \
  case triton::arch::ID_REG_X86_XMM ## index: {                           \
    auto val = value.convert_to<triton::uint128>();                       \
    std::memcpy((triton::uint128*)this->reg, &val, triton::size::dqword); \
  } break;                                                                \
}

#define YMM_WRITE(index, reg) {                                           \
  case triton::arch::ID_REG_X86_YMM ## index: {                           \
    auto val = value.convert_to<triton::uint256>();                       \
    std::memcpy((triton::uint256*)this->reg, &val, triton::size::qqword); \
  } break;                                                                \
}

#define GR_WRITE(name, reg, size) {                                    \
  case triton::arch::ID_REG_X86_ ## name: {                            \
    auto val = value.convert_to<triton::size>();                       \
    std::memcpy((triton::size*)this->reg, &val, sizeof(triton::size)); \
  } break;                                                             \
}

#define FLG_WRITE(name, reg, size, off) {                                 \
  case triton::arch::ID_REG_X86_ ## name: {                               \
    triton::size flag = 0;                                                \
    std::memcpy(&flag, (triton::size*)this->reg, sizeof(triton::size));   \
    flag = !value.is_zero() ? (flag | (1 << off)) : (flag & ~(1 << off)); \
    std::memcpy((triton::size*)this->reg, &flag, sizeof(triton::size));   \
  } break;                                                                \
}

namespace triton {
  namespace arch {
    namespace x86 {

      x86Cpu::x86Cpu(triton::callbacks::Callbacks* callbacks) : x86Specifications(ARCH_X86) {
        this->callbacks = callbacks;
        this->handle    = 0;

        this->clear();
        this->disassInit();
      }


      x86Cpu::x86Cpu(const x86Cpu& other) : x86Specifications(ARCH_X86) {
        this->copy(other);
      }


      x86Cpu::~x86Cpu() {
        this->memory.clear();
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }
      }


      void x86Cpu::disassInit(void) {
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }

        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_32, &this->handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x86Cpu::disassInit(): Cannot open capstone.");

        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);
      }


      void x86Cpu::copy(const x86Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        this->disassInit();

        std::memcpy(this->eax,        other.eax,        sizeof(this->eax));
        std::memcpy(this->ebx,        other.ebx,        sizeof(this->ebx));
        std::memcpy(this->ecx,        other.ecx,        sizeof(this->ecx));
        std::memcpy(this->edx,        other.edx,        sizeof(this->edx));
        std::memcpy(this->edi,        other.edi,        sizeof(this->edi));
        std::memcpy(this->esi,        other.esi,        sizeof(this->esi));
        std::memcpy(this->esp,        other.esp,        sizeof(this->esp));
        std::memcpy(this->ebp,        other.ebp,        sizeof(this->ebp));
        std::memcpy(this->eip,        other.eip,        sizeof(this->eip));
        std::memcpy(this->eflags,     other.eflags,     sizeof(this->eflags));
        std::memcpy(this->mm0,        other.mm0,        sizeof(this->mm0));
        std::memcpy(this->mm1,        other.mm1,        sizeof(this->mm1));
        std::memcpy(this->mm2,        other.mm2,        sizeof(this->mm2));
        std::memcpy(this->mm3,        other.mm3,        sizeof(this->mm3));
        std::memcpy(this->mm4,        other.mm4,        sizeof(this->mm4));
        std::memcpy(this->mm5,        other.mm5,        sizeof(this->mm5));
        std::memcpy(this->mm6,        other.mm6,        sizeof(this->mm6));
        std::memcpy(this->mm7,        other.mm7,        sizeof(this->mm7));
        std::memcpy(this->ymm0,       other.ymm0,       sizeof(this->ymm0));
        std::memcpy(this->ymm1,       other.ymm1,       sizeof(this->ymm1));
        std::memcpy(this->ymm2,       other.ymm2,       sizeof(this->ymm2));
        std::memcpy(this->ymm3,       other.ymm3,       sizeof(this->ymm3));
        std::memcpy(this->ymm4,       other.ymm4,       sizeof(this->ymm4));
        std::memcpy(this->ymm5,       other.ymm5,       sizeof(this->ymm5));
        std::memcpy(this->ymm6,       other.ymm6,       sizeof(this->ymm6));
        std::memcpy(this->ymm7,       other.ymm7,       sizeof(this->ymm7));
        std::memcpy(this->mxcsr,      other.mxcsr,      sizeof(this->mxcsr));
        std::memcpy(this->cr0,        other.cr0,        sizeof(this->cr0));
        std::memcpy(this->cr1,        other.cr1,        sizeof(this->cr1));
        std::memcpy(this->cr2,        other.cr2,        sizeof(this->cr2));
        std::memcpy(this->cr3,        other.cr3,        sizeof(this->cr3));
        std::memcpy(this->cr4,        other.cr4,        sizeof(this->cr4));
        std::memcpy(this->cr5,        other.cr5,        sizeof(this->cr5));
        std::memcpy(this->cr6,        other.cr6,        sizeof(this->cr6));
        std::memcpy(this->cr7,        other.cr7,        sizeof(this->cr7));
        std::memcpy(this->cr8,        other.cr8,        sizeof(this->cr8));
        std::memcpy(this->cr9,        other.cr9,        sizeof(this->cr9));
        std::memcpy(this->cr10,       other.cr10,       sizeof(this->cr10));
        std::memcpy(this->cr11,       other.cr11,       sizeof(this->cr11));
        std::memcpy(this->cr12,       other.cr12,       sizeof(this->cr12));
        std::memcpy(this->cr13,       other.cr13,       sizeof(this->cr13));
        std::memcpy(this->cr14,       other.cr14,       sizeof(this->cr14));
        std::memcpy(this->cr15,       other.cr15,       sizeof(this->cr15));
        std::memcpy(this->cs,         other.cs,         sizeof(this->cs));
        std::memcpy(this->ds,         other.ds,         sizeof(this->ds));
        std::memcpy(this->es,         other.es,         sizeof(this->es));
        std::memcpy(this->fs,         other.fs,         sizeof(this->fs));
        std::memcpy(this->gs,         other.gs,         sizeof(this->gs));
        std::memcpy(this->ss,         other.ss,         sizeof(this->ss));
        std::memcpy(this->dr0,        other.dr0,        sizeof(this->dr0));
        std::memcpy(this->dr1,        other.dr1,        sizeof(this->dr1));
        std::memcpy(this->dr2,        other.dr2,        sizeof(this->dr2));
        std::memcpy(this->dr3,        other.dr3,        sizeof(this->dr3));
        std::memcpy(this->dr6,        other.dr6,        sizeof(this->dr6));
        std::memcpy(this->dr7,        other.dr7,        sizeof(this->dr7));
        std::memcpy(this->mxcsr_mask, other.mxcsr_mask, sizeof(this->mxcsr_mask));
        std::memcpy(this->fcw,        other.fcw,        sizeof(this->fcw));
        std::memcpy(this->fsw,        other.fsw,        sizeof(this->fsw));
        std::memcpy(this->ftw,        other.ftw,        sizeof(this->ftw));
        std::memcpy(this->fop,        other.fop,        sizeof(this->fop));
        std::memcpy(this->fip,        other.fip,        sizeof(this->fip));
        std::memcpy(this->fcs,        other.fcs,        sizeof(this->fcs));
        std::memcpy(this->fdp,        other.fdp,        sizeof(this->fdp));
        std::memcpy(this->fds,        other.fds,        sizeof(this->fds));
        std::memcpy(this->efer,       other.efer,       sizeof(this->efer));
      }


      void x86Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->eax,        0x00, sizeof(this->eax));
        std::memset(this->ebx,        0x00, sizeof(this->ebx));
        std::memset(this->ecx,        0x00, sizeof(this->ecx));
        std::memset(this->edx,        0x00, sizeof(this->edx));
        std::memset(this->edi,        0x00, sizeof(this->edi));
        std::memset(this->esi,        0x00, sizeof(this->esi));
        std::memset(this->esp,        0x00, sizeof(this->esp));
        std::memset(this->ebp,        0x00, sizeof(this->ebp));
        std::memset(this->eip,        0x00, sizeof(this->eip));
        std::memset(this->eflags,     0x00, sizeof(this->eflags));
        std::memset(this->mm0,        0x00, sizeof(this->mm0));
        std::memset(this->mm1,        0x00, sizeof(this->mm1));
        std::memset(this->mm2,        0x00, sizeof(this->mm2));
        std::memset(this->mm3,        0x00, sizeof(this->mm3));
        std::memset(this->mm4,        0x00, sizeof(this->mm4));
        std::memset(this->mm5,        0x00, sizeof(this->mm5));
        std::memset(this->mm6,        0x00, sizeof(this->mm6));
        std::memset(this->mm7,        0x00, sizeof(this->mm7));
        std::memset(this->ymm0,       0x00, sizeof(this->ymm0));
        std::memset(this->ymm1,       0x00, sizeof(this->ymm1));
        std::memset(this->ymm2,       0x00, sizeof(this->ymm2));
        std::memset(this->ymm3,       0x00, sizeof(this->ymm3));
        std::memset(this->ymm4,       0x00, sizeof(this->ymm4));
        std::memset(this->ymm5,       0x00, sizeof(this->ymm5));
        std::memset(this->ymm6,       0x00, sizeof(this->ymm6));
        std::memset(this->ymm7,       0x00, sizeof(this->ymm7));
        std::memset(this->mxcsr,      0x00, sizeof(this->mxcsr));
        std::memset(this->cr0,        0x00, sizeof(this->cr0));
        std::memset(this->cr1,        0x00, sizeof(this->cr1));
        std::memset(this->cr2,        0x00, sizeof(this->cr2));
        std::memset(this->cr3,        0x00, sizeof(this->cr3));
        std::memset(this->cr4,        0x00, sizeof(this->cr4));
        std::memset(this->cr5,        0x00, sizeof(this->cr5));
        std::memset(this->cr6,        0x00, sizeof(this->cr6));
        std::memset(this->cr7,        0x00, sizeof(this->cr7));
        std::memset(this->cr8,        0x00, sizeof(this->cr8));
        std::memset(this->cr9,        0x00, sizeof(this->cr9));
        std::memset(this->cr10,       0x00, sizeof(this->cr10));
        std::memset(this->cr11,       0x00, sizeof(this->cr11));
        std::memset(this->cr12,       0x00, sizeof(this->cr12));
        std::memset(this->cr13,       0x00, sizeof(this->cr13));
        std::memset(this->cr14,       0x00, sizeof(this->cr14));
        std::memset(this->cr15,       0x00, sizeof(this->cr15));
        std::memset(this->cs,         0x00, sizeof(this->cs));
        std::memset(this->ds,         0x00, sizeof(this->ds));
        std::memset(this->es,         0x00, sizeof(this->es));
        std::memset(this->fs,         0x00, sizeof(this->fs));
        std::memset(this->gs,         0x00, sizeof(this->gs));
        std::memset(this->ss,         0x00, sizeof(this->ss));
        std::memset(this->dr0,        0x00, sizeof(this->dr0));
        std::memset(this->dr1,        0x00, sizeof(this->dr1));
        std::memset(this->dr2,        0x00, sizeof(this->dr2));
        std::memset(this->dr3,        0x00, sizeof(this->dr3));
        std::memset(this->dr6,        0x00, sizeof(this->dr6));
        std::memset(this->dr7,        0x00, sizeof(this->dr7));
        std::memset(this->mxcsr_mask, 0x00, sizeof(this->mxcsr_mask));
        std::memset(this->fcw,        0x00, sizeof(this->fcw));
        std::memset(this->fsw,        0x00, sizeof(this->fsw));
        std::memset(this->ftw,        0x00, sizeof(this->ftw));
        std::memset(this->fop,        0x00, sizeof(this->fop));
        std::memset(this->fip,        0x00, sizeof(this->fip));
        std::memset(this->fcs,        0x00, sizeof(this->fcs));
        std::memset(this->fdp,        0x00, sizeof(this->fdp));
        std::memset(this->fds,        0x00, sizeof(this->fds));
        std::memset(this->efer,       0x00, sizeof(this->efer));
      }


      x86Cpu& x86Cpu::operator=(const x86Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e x86Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool x86Cpu::isFlag(triton::arch::register_e regId) const {
        if (regId >= triton::arch::ID_REG_X86_AC && regId <= triton::arch::ID_REG_X86_FSW_B) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FTW && regId <= triton::arch::ID_REG_X86_FDP) { return true; }
        if (regId >= triton::arch::ID_REG_X86_SSE_IE && regId <= triton::arch::ID_REG_X86_SSE_FZ) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FCW_IM && regId <= triton::arch::ID_REG_X86_FCW_X) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FSW_IE && regId <= triton::arch::ID_REG_X86_FSW_B) { return true; }
        return false;
      }


      bool x86Cpu::isRegister(triton::arch::register_e regId) const {
        return (
          this->isGPR(regId)      ||
          this->isMMX(regId)      ||
          this->isSSE(regId)      ||
          this->isFPU(regId)      ||
          this->isEFER(regId)     ||
          this->isAVX256(regId)   ||
          this->isControl(regId)  ||
          this->isDebug(regId)    ||
          this->isSegment(regId)
        );
      }


      bool x86Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x86Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_EAX && regId <= triton::arch::ID_REG_X86_EFLAGS) ? true : false);
      }


      bool x86Cpu::isMMX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MM0 && regId <= triton::arch::ID_REG_X86_MM7) ? true : false);
      }


      bool x86Cpu::isSSE(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MXCSR && regId <= triton::arch::ID_REG_X86_XMM7) ? true : false);
      }


      bool x86Cpu::isFPU(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_FTW && regId <= triton::arch::ID_REG_X86_FDP) ? true : false);
      }


      bool x86Cpu::isEFER(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_EFER && regId <= triton::arch::ID_REG_X86_EFER) ? true : false);
      }


      bool x86Cpu::isAVX256(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_YMM0 && regId <= triton::arch::ID_REG_X86_YMM7) ? true : false);
      }


      bool x86Cpu::isControl(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CR0 && regId <= triton::arch::ID_REG_X86_CR15) ? true : false);
      }


      bool x86Cpu::isDebug(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_DR0 && regId <= triton::arch::ID_REG_X86_DR7) ? true : false);
      }


      bool x86Cpu::isSegment(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CS && regId <= triton::arch::ID_REG_X86_SS) ? true : false);
      }


      triton::uint32 x86Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 x86Cpu::gprSize(void) const {
        return triton::size::dword;
      }


      triton::uint32 x86Cpu::gprBitSize(void) const {
        return triton::bitsize::dword;
      }



      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& x86Cpu::getAllRegisters(void) const {
        return this->registers_;
      }


      std::set<const triton::arch::Register*> x86Cpu::getParentRegisters(void) const {
        std::set<const triton::arch::Register*> ret;

        for (const auto& kv: this->registers_) {
          auto regId = kv.first;
          const auto& reg = kv.second;

          /* Add GPR */
          if (reg.getSize() == this->gprSize())
            ret.insert(&reg);

          /* Add Flags */
          else if (this->isFlag(regId))
            ret.insert(&reg);

          /* Add MMX */
          else if (this->isMMX(regId))
            ret.insert(&reg);

          /* Add SSE */
          else if (this->isSSE(regId))
            ret.insert(&reg);

          /* Add FPU */
          else if (this->isFPU(regId))
            ret.insert(&reg);

          /* Add EFER */
          else if (this->isEFER(regId))
            ret.insert(&reg);

          /* Add AVX-256 */
          else if (this->isAVX256(regId))
            ret.insert(&reg);

          /* Add Control */
          else if (this->isControl(regId))
            ret.insert(&reg);

          /* Add Debug */
          else if (this->isDebug(regId))
            ret.insert(&reg);

          /* Add Segment */
          else if (this->isSegment(regId))
            ret.insert(&reg);
        }

        return ret;
      }


      const triton::arch::Register& x86Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->registers_.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x86Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x86Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& x86Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& x86Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& x86Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }


      void x86Cpu::disassembly(triton::arch::Instruction& inst) const {
        triton::extlibs::capstone::cs_insn* insn;
        triton::usize count = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Opcode and opcodeSize must be definied.");

        /* Clear instructicon's operands if alredy defined */
        inst.operands.clear();

        /* Let's disass and build our operands */
        count = triton::extlibs::capstone::cs_disasm(this->handle, inst.getOpcode(), inst.getSize(), inst.getAddress(), 0, &insn);
        if (count > 0) {
          /* Detail information */
          triton::extlibs::capstone::cs_detail* detail = insn->detail;

          /* Init the disassembly */
          std::stringstream str;

          str << insn[0].mnemonic;
          if (detail->x86.op_count)
            str << " " <<  insn[0].op_str;

          inst.setDisassembly(str.str());

          /* Refine the size */
          inst.setSize(insn[0].size);

          /* Init the instruction's type */
          inst.setType(this->capstoneInstructionToTritonInstruction(insn[0].id));

          /* Init the instruction's prefix */
          inst.setPrefix(this->capstonePrefixToTritonPrefix(detail->x86.prefix[0]));

          /* Init operands */
          for (triton::uint32 n = 0; n < detail->x86.op_count; n++) {
            triton::extlibs::capstone::cs_x86_op* op = &(detail->x86.operands[n]);
            switch(op->type) {

              case triton::extlibs::capstone::X86_OP_IMM:
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Immediate(op->imm, op->size)));
                break;

              case triton::extlibs::capstone::X86_OP_MEM: {
                triton::arch::MemoryAccess mem;

                /* Set the size of the memory access */
                mem.setPair(std::make_pair(((op->size * triton::bitsize::byte) - 1), 0));

                /* LEA if exists */
                const triton::arch::Register segment(*this, this->capstoneRegisterToTritonRegister(op->mem.segment));
                const triton::arch::Register base(*this, this->capstoneRegisterToTritonRegister(op->mem.base));
                const triton::arch::Register index(*this, this->capstoneRegisterToTritonRegister(op->mem.index));

                triton::uint32 immsize = (
                                          this->isRegisterValid(base.getId()) ? base.getSize() :
                                          this->isRegisterValid(index.getId()) ? index.getSize() :
                                          this->gprSize()
                                        );

                triton::arch::Immediate disp(op->mem.disp, immsize);
                triton::arch::Immediate scale(op->mem.scale, immsize);

                /* Specify that LEA contains a PC relative */
                if (base.getId() == this->pcId)
                  mem.setPcRelative(inst.getNextAddress());

                mem.setSegmentRegister(segment);
                mem.setBaseRegister(base);
                mem.setIndexRegister(index);
                mem.setDisplacement(disp);
                mem.setScale(scale);

                inst.operands.push_back(triton::arch::OperandWrapper(mem));
                break;
              }

              case triton::extlibs::capstone::X86_OP_REG:
                inst.operands.push_back(triton::arch::OperandWrapper(triton::arch::Register(*this, this->capstoneRegisterToTritonRegister(op->reg))));
                break;

              default:
                break;
            }

          }
          /* Set branch */
          if (detail->groups_count > 0) {
            for (triton::uint32 n = 0; n < detail->groups_count; n++) {
              if (detail->groups[n] == triton::extlibs::capstone::X86_GRP_JUMP)
                inst.setBranch(true);
              if (detail->groups[n] == triton::extlibs::capstone::X86_GRP_JUMP ||
                  detail->groups[n] == triton::extlibs::capstone::X86_GRP_CALL ||
                  detail->groups[n] == triton::extlibs::capstone::X86_GRP_RET)
                inst.setControlFlow(true);
            }
          }
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("x86Cpu::disassembly(): Failed to disassemble the given code.");
      }


      triton::uint8 x86Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte));

        auto it = this->memory.find(addr);
        if (it == this->memory.end())
          return 0x00;

        return it->second;
      }


      triton::uint512 x86Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x86Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << triton::bitsize::byte) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> x86Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index));

        return area;
      }


      triton::uint512 x86Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {

          GRP_READ_2(A, eax);
          GRP_READ_2(B, ebx);
          GRP_READ_2(C, ecx);
          GRP_READ_2(D, edx);

          GRP_READ_3(DI, edi)
          GRP_READ_3(SI, esi)
          GRP_READ_3(SP, esp)
          GRP_READ_3(BP, ebp)

          GRP_READ_4(IP, eip)

          GR_READ(EFLAGS, eflags, uint32)

          MMX_READ(0, mm0)
          MMX_READ(1, mm1)
          MMX_READ(2, mm2)
          MMX_READ(3, mm3)
          MMX_READ(4, mm4)
          MMX_READ(5, mm5)
          MMX_READ(6, mm6)
          MMX_READ(7, mm7)

          XMM_READ(0, ymm0)
          XMM_READ(1, ymm1)
          XMM_READ(2, ymm2)
          XMM_READ(3, ymm3)
          XMM_READ(4, ymm4)
          XMM_READ(5, ymm5)
          XMM_READ(6, ymm6)
          XMM_READ(7, ymm7)

          YMM_READ(0, ymm0)
          YMM_READ(1, ymm1)
          YMM_READ(2, ymm2)
          YMM_READ(3, ymm3)
          YMM_READ(4, ymm4)
          YMM_READ(5, ymm5)
          YMM_READ(6, ymm6)
          YMM_READ(7, ymm7)

          GR_READ(MXCSR, mxcsr, uint32)
          GR_READ(MXCSR_MASK, mxcsr_mask, uint32)

          CRR_READ(0, cr0)
          CRR_READ(1, cr1)
          CRR_READ(2, cr2)
          CRR_READ(3, cr3)
          CRR_READ(4, cr4)
          CRR_READ(5, cr5)
          CRR_READ(6, cr6)
          CRR_READ(7, cr7)
          CRR_READ(8, cr8)
          CRR_READ(9, cr9)
          CRR_READ(10, cr10)
          CRR_READ(11, cr11)
          CRR_READ(12, cr12)
          CRR_READ(13, cr13)
          CRR_READ(14, cr14)
          CRR_READ(15, cr15)

          DRR_READ(0, dr0)
          DRR_READ(1, dr1)
          DRR_READ(2, dr2)
          DRR_READ(3, dr3)
          DRR_READ(4, dr4)
          DRR_READ(5, dr5)
          DRR_READ(6, dr6)
          DRR_READ(7, dr7)

          FLG_READ(SSE_IE, mxcsr, uint32, 0)
          FLG_READ(SSE_DE, mxcsr, uint32, 1)
          FLG_READ(SSE_ZE, mxcsr, uint32, 2)
          FLG_READ(SSE_OE, mxcsr, uint32, 3)
          FLG_READ(SSE_UE, mxcsr, uint32, 4)
          FLG_READ(SSE_PE, mxcsr, uint32, 5)
          FLG_READ(SSE_DAZ, mxcsr, uint32, 6)
          FLG_READ(SSE_IM, mxcsr, uint32, 7)
          FLG_READ(SSE_DM, mxcsr, uint32, 8)
          FLG_READ(SSE_ZM, mxcsr, uint32, 9)
          FLG_READ(SSE_OM, mxcsr, uint32, 10)
          FLG_READ(SSE_UM, mxcsr, uint32, 11)
          FLG_READ(SSE_PM, mxcsr, uint32, 12)
          FLG_READ(SSE_RL, mxcsr, uint32, 13)
          FLG_READ(SSE_RH, mxcsr, uint32, 14)
          FLG_READ(SSE_FZ, mxcsr, uint32, 15)

          FLG_READ(CF,  eflags, uint32, 0)
          FLG_READ(PF,  eflags, uint32, 2)
          FLG_READ(AF,  eflags, uint32, 4)
          FLG_READ(ZF,  eflags, uint32, 6)
          FLG_READ(SF,  eflags, uint32, 7)
          FLG_READ(TF,  eflags, uint32, 8)
          FLG_READ(IF,  eflags, uint32, 9)
          FLG_READ(DF,  eflags, uint32, 10)
          FLG_READ(OF,  eflags, uint32, 11)
          FLG_READ(NT,  eflags, uint32, 14)
          FLG_READ(RF,  eflags, uint32, 16)
          FLG_READ(VM,  eflags, uint32, 17)
          FLG_READ(AC,  eflags, uint32, 18)
          FLG_READ(VIF, eflags, uint32, 19)
          FLG_READ(VIP, eflags, uint32, 20)
          FLG_READ(ID,  eflags, uint32, 21)

          SEG_READ(CS, cs)
          SEG_READ(DS, ds)
          SEG_READ(ES, es)
          SEG_READ(FS, fs)
          SEG_READ(GS, gs)
          SEG_READ(SS, ss)

          GR_READ(FIP, fip, uint64)
          GR_READ(FDP, fdp, uint64)
          GR_READ(FCW, fcw, uint16)
          GR_READ(FSW, fsw, uint16)
          GR_READ(FOP, fop, uint16)
          GR_READ(FCS, fcs, uint16)
          GR_READ(FDS, fds, uint16)
          GR_READ(FTW, ftw, uint16)

          FLG_READ(FCW_IM, fcw, uint16, 0)
          FLG_READ(FCW_DM, fcw, uint16, 1)
          FLG_READ(FCW_ZM, fcw, uint16, 2)
          FLG_READ(FCW_OM, fcw, uint16, 3)
          FLG_READ(FCW_UM, fcw, uint16, 4)
          FLG_READ(FCW_PM, fcw, uint16, 5)
          FLG_READ(FCW_PC, fcw, uint16, 8)
          FLG_READ(FCW_RC, fcw, uint16, 10)
          FLG_READ(FCW_X, fcw, uint16, 12)

          FLG_READ(FSW_IE, fsw, uint16, 0)
          FLG_READ(FSW_DE, fsw, uint16, 1)
          FLG_READ(FSW_ZE, fsw, uint16, 2)
          FLG_READ(FSW_OE, fsw, uint16, 3)
          FLG_READ(FSW_UE, fsw, uint16, 4)
          FLG_READ(FSW_PE, fsw, uint16, 5)
          FLG_READ(FSW_SF, fsw, uint16, 6)
          FLG_READ(FSW_ES, fsw, uint16, 7)
          FLG_READ(FSW_C0, fsw, uint16, 8)
          FLG_READ(FSW_C1, fsw, uint16, 9)
          FLG_READ(FSW_C2, fsw, uint16, 10)
          FLG_READ(FSW_TOP, fsw, uint16, 11)
          FLG_READ(FSW_C3, fsw, uint16, 14)
          FLG_READ(FSW_B, fsw, uint16, 15)

          FLG_READ(EFER_SCE, efer, uint64, 0)
          FLG_READ(EFER_LME, efer, uint64, 8)
          FLG_READ(EFER_LMA, efer, uint64, 10)
          FLG_READ(EFER_NXE, efer, uint64, 11)
          FLG_READ(EFER_SVME, efer, uint64, 12)
          FLG_READ(EFER_LMSLE, efer, uint64, 13)
          FLG_READ(EFER_FFXSR, efer, uint64, 14)
          FLG_READ(EFER_TCE, efer, uint64, 15)

          GR_READ(EFER, efer, uint64)

          default:
            throw triton::exceptions::Cpu("x86Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x86Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte), value);
        this->memory[addr] = value;
      }


      void x86Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("x86Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x86Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
          cv >>= 8;
        }
      }


      void x86Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index]);
        }
      }


      void x86Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, area[index]);
        }
      }


      void x86Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("x86Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {

          GRP_WRITE_2(A, eax);
          GRP_WRITE_2(B, ebx);
          GRP_WRITE_2(C, ecx);
          GRP_WRITE_2(D, edx);

          GRP_WRITE_3(DI, edi)
          GRP_WRITE_3(SI, esi)
          GRP_WRITE_3(SP, esp)
          GRP_WRITE_3(BP, ebp)

          GRP_WRITE_4(IP, eip)

          GR_WRITE(EFLAGS, eflags, uint32)

          MMX_WRITE(0, mm0)
          MMX_WRITE(1, mm1)
          MMX_WRITE(2, mm2)
          MMX_WRITE(3, mm3)
          MMX_WRITE(4, mm4)
          MMX_WRITE(5, mm5)
          MMX_WRITE(6, mm6)
          MMX_WRITE(7, mm7)

          XMM_WRITE(0, ymm0)
          XMM_WRITE(1, ymm1)
          XMM_WRITE(2, ymm2)
          XMM_WRITE(3, ymm3)
          XMM_WRITE(4, ymm4)
          XMM_WRITE(5, ymm5)
          XMM_WRITE(6, ymm6)
          XMM_WRITE(7, ymm7)

          YMM_WRITE(0, ymm0)
          YMM_WRITE(1, ymm1)
          YMM_WRITE(2, ymm2)
          YMM_WRITE(3, ymm3)
          YMM_WRITE(4, ymm4)
          YMM_WRITE(5, ymm5)
          YMM_WRITE(6, ymm6)
          YMM_WRITE(7, ymm7)

          GR_WRITE(MXCSR, mxcsr, uint32)
          GR_WRITE(MXCSR_MASK, mxcsr_mask, uint32)

          CRR_WRITE(0,  cr0)
          CRR_WRITE(1,  cr1)
          CRR_WRITE(2,  cr2)
          CRR_WRITE(3,  cr3)
          CRR_WRITE(4,  cr4)
          CRR_WRITE(5,  cr5)
          CRR_WRITE(6,  cr6)
          CRR_WRITE(7,  cr7)
          CRR_WRITE(8,  cr8)
          CRR_WRITE(9,  cr9)
          CRR_WRITE(10, cr10)
          CRR_WRITE(11, cr11)
          CRR_WRITE(12, cr12)
          CRR_WRITE(13, cr13)
          CRR_WRITE(14, cr14)
          CRR_WRITE(15, cr15)

          DRR_WRITE(0, dr0)
          DRR_WRITE(1, dr1)
          DRR_WRITE(2, dr2)
          DRR_WRITE(3, dr3)
          DRR_WRITE(4, dr4)
          DRR_WRITE(5, dr5)
          DRR_WRITE(6, dr6)
          DRR_WRITE(7, dr7)

          FLG_WRITE(SSE_IE,  mxcsr, uint32, 0)
          FLG_WRITE(SSE_DE,  mxcsr, uint32, 1)
          FLG_WRITE(SSE_ZE,  mxcsr, uint32, 2)
          FLG_WRITE(SSE_OE,  mxcsr, uint32, 3)
          FLG_WRITE(SSE_UE,  mxcsr, uint32, 4)
          FLG_WRITE(SSE_PE,  mxcsr, uint32, 5)
          FLG_WRITE(SSE_DAZ, mxcsr, uint32, 6)
          FLG_WRITE(SSE_IM,  mxcsr, uint32, 7)
          FLG_WRITE(SSE_DM,  mxcsr, uint32, 8)
          FLG_WRITE(SSE_ZM,  mxcsr, uint32, 9)
          FLG_WRITE(SSE_OM,  mxcsr, uint32, 10)
          FLG_WRITE(SSE_UM,  mxcsr, uint32, 11)
          FLG_WRITE(SSE_PM,  mxcsr, uint32, 12)
          FLG_WRITE(SSE_RL,  mxcsr, uint32, 13)
          FLG_WRITE(SSE_RH,  mxcsr, uint32, 14)
          FLG_WRITE(SSE_FZ,  mxcsr, uint32, 15)

          FLG_WRITE(CF,  eflags, uint32, 0)
          FLG_WRITE(PF,  eflags, uint32, 2)
          FLG_WRITE(AF,  eflags, uint32, 4)
          FLG_WRITE(ZF,  eflags, uint32, 6)
          FLG_WRITE(SF,  eflags, uint32, 7)
          FLG_WRITE(TF,  eflags, uint32, 8)
          FLG_WRITE(IF,  eflags, uint32, 9)
          FLG_WRITE(DF,  eflags, uint32, 10)
          FLG_WRITE(OF,  eflags, uint32, 11)
          FLG_WRITE(NT,  eflags, uint32, 14)
          FLG_WRITE(RF,  eflags, uint32, 16)
          FLG_WRITE(VM,  eflags, uint32, 17)
          FLG_WRITE(AC,  eflags, uint32, 18)
          FLG_WRITE(VIF, eflags, uint32, 19)
          FLG_WRITE(VIP, eflags, uint32, 20)
          FLG_WRITE(ID,  eflags, uint32, 21)

          SEG_WRITE(CS, cs)
          SEG_WRITE(DS, ds)
          SEG_WRITE(ES, es)
          SEG_WRITE(FS, fs)
          SEG_WRITE(GS, gs)
          SEG_WRITE(SS, ss)

          GR_WRITE(FIP, fip, uint64)
          GR_WRITE(FDP, fdp, uint64)
          GR_WRITE(FCW, fcw, uint16)
          GR_WRITE(FSW, fsw, uint16)
          GR_WRITE(FOP, fop, uint16)
          GR_WRITE(FCS, fcs, uint16)
          GR_WRITE(FDS, fds, uint16)
          GR_WRITE(FTW, ftw, uint16)

          FLG_WRITE(FCW_IM, fcw, uint16, 0)
          FLG_WRITE(FCW_DM, fcw, uint16, 1)
          FLG_WRITE(FCW_ZM, fcw, uint16, 2)
          FLG_WRITE(FCW_OM, fcw, uint16, 3)
          FLG_WRITE(FCW_UM, fcw, uint16, 4)
          FLG_WRITE(FCW_PM, fcw, uint16, 5)
          FLG_WRITE(FCW_PC, fcw, uint16, 8)
          FLG_WRITE(FCW_RC, fcw, uint16, 10)
          FLG_WRITE(FCW_X,  fcw, uint16, 12)

          FLG_WRITE(FSW_IE,  fsw, uint16, 0)
          FLG_WRITE(FSW_DE,  fsw, uint16, 1)
          FLG_WRITE(FSW_ZE,  fsw, uint16, 2)
          FLG_WRITE(FSW_OE,  fsw, uint16, 3)
          FLG_WRITE(FSW_UE,  fsw, uint16, 4)
          FLG_WRITE(FSW_PE,  fsw, uint16, 5)
          FLG_WRITE(FSW_SF,  fsw, uint16, 6)
          FLG_WRITE(FSW_ES,  fsw, uint16, 7)
          FLG_WRITE(FSW_C0,  fsw, uint16, 8)
          FLG_WRITE(FSW_C1,  fsw, uint16, 9)
          FLG_WRITE(FSW_C2,  fsw, uint16, 10)
          FLG_WRITE(FSW_TOP, fsw, uint16, 11)
          FLG_WRITE(FSW_C3,  fsw, uint16, 14)
          FLG_WRITE(FSW_B,   fsw, uint16, 15)

          FLG_WRITE(EFER_SCE,   efer, uint64, 0)
          FLG_WRITE(EFER_LME,   efer, uint64, 8)
          FLG_WRITE(EFER_LMA,   efer, uint64, 10)
          FLG_WRITE(EFER_NXE,   efer, uint64, 11)
          FLG_WRITE(EFER_SVME,  efer, uint64, 12)
          FLG_WRITE(EFER_LMSLE, efer, uint64, 13)
          FLG_WRITE(EFER_FFXSR, efer, uint64, 14)
          FLG_WRITE(EFER_TCE,   efer, uint64, 15)

          GR_WRITE(EFER, efer, uint64)

          default:
            throw triton::exceptions::Cpu("x86Cpu:setConcreteRegisterValue() - Invalid register.");
        }
      }


      bool x86Cpu::isThumb(void) const {
        /* There is no thumb mode in x86 */
        return false;
      }


      void x86Cpu::setThumb(bool state) {
        /* There is no thumb mode in x86 */
      }


      bool x86Cpu::isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const {
        return this->isConcreteMemoryValueDefined(mem.getAddress(), mem.getSize());
      }


      bool x86Cpu::isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size) const {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end())
            return false;
        }
        return true;
      }


      void x86Cpu::clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
        this->clearConcreteMemoryValue(mem.getAddress(), mem.getSize());
      }


      void x86Cpu::clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end()) {
            this->memory.erase(baseAddr + index);
          }
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */
