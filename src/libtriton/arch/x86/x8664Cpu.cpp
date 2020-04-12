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
#include <triton/x8664Cpu.hpp>

// Read macros

#define GRP_READ_1(name, reg) {                                         \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## D: {                        \
    triton::uint32 val = 0;                                             \
    std::memcpy(&val, (triton::uint32*)this->reg, triton::size::dword); \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## W: {                        \
    triton::uint16 val = 0;                                             \
    std::memcpy(&val, (triton::uint16*)this->reg, triton::size::word);  \
    return val;                                                         \
  }                                                                     \
  case triton::arch::ID_REG_X86_ ## name ## B: {                        \
    triton::uint8 val = 0;                                              \
    std::memcpy(&val, (triton::uint8*)this->reg, triton::size::byte);   \
    return val;                                                         \
  }                                                                     \
}

#define GRP_READ_2(name, reg) {                                         \
  case triton::arch::ID_REG_X86_R ## name ## X: {                       \
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
    return val;                                                         \
  }                                                                     \
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
  case triton::arch::ID_REG_X86_R ## name: {                            \
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
    return val;                                                         \
  }                                                                     \
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
  case triton::arch::ID_REG_X86_R ## name: {                            \
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
    return val;                                                         \
  }                                                                     \
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
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
    return val;                                                         \
  }                                                                     \
}

#define DRR_READ(index, reg) {                                          \
  case triton::arch::ID_REG_X86_DR ## index: {                          \
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
    return val;                                                         \
  }                                                                     \
}

#define SEG_READ(name, reg) {                                           \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    triton::uint64 val = 0;                                             \
    std::memcpy(&val, (triton::uint64*)this->reg, triton::size::qword); \
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

#define ZMM_READ(index, reg) {                                              \
  case triton::arch::ID_REG_X86_ZMM ## index: {                             \
    triton::uint512 val = 0;                                                \
    std::memcpy(&val, (triton::uint512*)this->reg, triton::size::dqqword);  \
    return val;                                                             \
  }                                                                         \
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

#define GRP_WRITE_1(name, reg) {                                        \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    auto val = value.convert_to<triton::uint64>();                      \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword); \
  } break;                                                              \
  case triton::arch::ID_REG_X86_ ## name ## D: {                        \
    auto val = value.convert_to<triton::uint32>();                      \
    std::memcpy((triton::uint32*)this->reg, &val, triton::size::dword); \
  } break;                                                              \
  case triton::arch::ID_REG_X86_ ## name ## W: {                        \
    auto val = value.convert_to<triton::uint16>();                      \
    std::memcpy((triton::uint16*)this->reg, &val, triton::size::word);  \
  } break;                                                              \
  case triton::arch::ID_REG_X86_ ## name ## B: {                        \
    auto val = value.convert_to<triton::uint8>();                       \
    std::memcpy((triton::uint8*)this->reg, &val, triton::size::byte);   \
  } break;                                                              \
}

#define GRP_WRITE_2(name, reg) {                                          \
  case triton::arch::ID_REG_X86_R ## name ## X: {                         \
    auto val = value.convert_to<triton::uint64>();                        \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword);   \
  } break;                                                                \
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
  case triton::arch::ID_REG_X86_R ## name: {                            \
    auto val = value.convert_to<triton::uint64>();                      \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword); \
  } break;                                                              \
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
  case triton::arch::ID_REG_X86_R ## name: {                            \
    auto val = value.convert_to<triton::uint64>();                      \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword); \
  } break;                                                              \
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
    auto val = value.convert_to<triton::uint64>();                      \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword); \
  } break;                                                              \
}

#define DRR_WRITE(index, reg) {                                         \
  case triton::arch::ID_REG_X86_DR ## index: {                          \
    auto val = value.convert_to<triton::uint64>();                      \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword); \
  } break;                                                              \
}

#define SEG_WRITE(name, reg) {                                          \
  case triton::arch::ID_REG_X86_ ## name: {                             \
    auto val = value.convert_to<triton::uint64>();                      \
    std::memcpy((triton::uint64*)this->reg, &val, triton::size::qword); \
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

#define ZMM_WRITE(index, reg) {                                             \
  case triton::arch::ID_REG_X86_ZMM ## index: {                             \
    auto val = value.convert_to<triton::uint512>();                         \
    std::memcpy((triton::uint512*)this->reg, &val, triton::size::dqqword);  \
  } break;                                                                  \
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

      x8664Cpu::x8664Cpu(triton::callbacks::Callbacks* callbacks) : x86Specifications(ARCH_X86_64) {
        this->callbacks = callbacks;
        this->handle    = 0;

        this->clear();
        this->disassInit();
      }


      x8664Cpu::x8664Cpu(const x8664Cpu& other) : x86Specifications(ARCH_X86_64) {
        this->copy(other);
      }


      x8664Cpu::~x8664Cpu() {
        this->memory.clear();
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }
      }


      void x8664Cpu::disassInit(void) {
        if (this->handle) {
          triton::extlibs::capstone::cs_close(&this->handle);
        }

        if (triton::extlibs::capstone::cs_open(triton::extlibs::capstone::CS_ARCH_X86, triton::extlibs::capstone::CS_MODE_64, &this->handle) != triton::extlibs::capstone::CS_ERR_OK)
          throw triton::exceptions::Disassembly("x8664Cpu::disassInit(): Cannot open capstone.");

        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_DETAIL, triton::extlibs::capstone::CS_OPT_ON);
        triton::extlibs::capstone::cs_option(this->handle, triton::extlibs::capstone::CS_OPT_SYNTAX, triton::extlibs::capstone::CS_OPT_SYNTAX_INTEL);
      }


      void x8664Cpu::copy(const x8664Cpu& other) {
        this->callbacks = other.callbacks;
        this->memory    = other.memory;

        this->disassInit();

        std::memcpy(this->rax,        other.rax,        sizeof(this->rax));
        std::memcpy(this->rbx,        other.rbx,        sizeof(this->rbx));
        std::memcpy(this->rcx,        other.rcx,        sizeof(this->rcx));
        std::memcpy(this->rdx,        other.rdx,        sizeof(this->rdx));
        std::memcpy(this->rdi,        other.rdi,        sizeof(this->rdi));
        std::memcpy(this->rsi,        other.rsi,        sizeof(this->rsi));
        std::memcpy(this->rsp,        other.rsp,        sizeof(this->rsp));
        std::memcpy(this->rbp,        other.rbp,        sizeof(this->rbp));
        std::memcpy(this->rip,        other.rip,        sizeof(this->rip));
        std::memcpy(this->eflags,     other.eflags,     sizeof(this->eflags));
        std::memcpy(this->r8,         other.r8,         sizeof(this->r8));
        std::memcpy(this->r9,         other.r9,         sizeof(this->r9));
        std::memcpy(this->r10,        other.r10,        sizeof(this->r10));
        std::memcpy(this->r11,        other.r11,        sizeof(this->r11));
        std::memcpy(this->r12,        other.r12,        sizeof(this->r12));
        std::memcpy(this->r13,        other.r13,        sizeof(this->r13));
        std::memcpy(this->r14,        other.r14,        sizeof(this->r14));
        std::memcpy(this->r15,        other.r15,        sizeof(this->r15));
        std::memcpy(this->mm0,        other.mm0,        sizeof(this->mm0));
        std::memcpy(this->mm1,        other.mm1,        sizeof(this->mm1));
        std::memcpy(this->mm2,        other.mm2,        sizeof(this->mm2));
        std::memcpy(this->mm3,        other.mm3,        sizeof(this->mm3));
        std::memcpy(this->mm4,        other.mm4,        sizeof(this->mm4));
        std::memcpy(this->mm5,        other.mm5,        sizeof(this->mm5));
        std::memcpy(this->mm6,        other.mm6,        sizeof(this->mm6));
        std::memcpy(this->mm7,        other.mm7,        sizeof(this->mm7));
        std::memcpy(this->zmm0,       other.zmm0,       sizeof(this->zmm0));
        std::memcpy(this->zmm1,       other.zmm1,       sizeof(this->zmm1));
        std::memcpy(this->zmm2,       other.zmm2,       sizeof(this->zmm2));
        std::memcpy(this->zmm3,       other.zmm3,       sizeof(this->zmm3));
        std::memcpy(this->zmm4,       other.zmm4,       sizeof(this->zmm4));
        std::memcpy(this->zmm5,       other.zmm5,       sizeof(this->zmm5));
        std::memcpy(this->zmm6,       other.zmm6,       sizeof(this->zmm6));
        std::memcpy(this->zmm7,       other.zmm7,       sizeof(this->zmm7));
        std::memcpy(this->zmm8,       other.zmm8,       sizeof(this->zmm8));
        std::memcpy(this->zmm9,       other.zmm9,       sizeof(this->zmm9));
        std::memcpy(this->zmm10,      other.zmm10,      sizeof(this->zmm10));
        std::memcpy(this->zmm11,      other.zmm11,      sizeof(this->zmm11));
        std::memcpy(this->zmm12,      other.zmm12,      sizeof(this->zmm12));
        std::memcpy(this->zmm13,      other.zmm13,      sizeof(this->zmm13));
        std::memcpy(this->zmm14,      other.zmm14,      sizeof(this->zmm14));
        std::memcpy(this->zmm15,      other.zmm15,      sizeof(this->zmm15));
        std::memcpy(this->zmm16,      other.zmm16,      sizeof(this->zmm16));
        std::memcpy(this->zmm17,      other.zmm17,      sizeof(this->zmm17));
        std::memcpy(this->zmm18,      other.zmm18,      sizeof(this->zmm18));
        std::memcpy(this->zmm19,      other.zmm19,      sizeof(this->zmm19));
        std::memcpy(this->zmm20,      other.zmm20,      sizeof(this->zmm20));
        std::memcpy(this->zmm21,      other.zmm21,      sizeof(this->zmm21));
        std::memcpy(this->zmm22,      other.zmm22,      sizeof(this->zmm22));
        std::memcpy(this->zmm23,      other.zmm23,      sizeof(this->zmm23));
        std::memcpy(this->zmm24,      other.zmm24,      sizeof(this->zmm24));
        std::memcpy(this->zmm25,      other.zmm25,      sizeof(this->zmm25));
        std::memcpy(this->zmm26,      other.zmm26,      sizeof(this->zmm26));
        std::memcpy(this->zmm27,      other.zmm27,      sizeof(this->zmm27));
        std::memcpy(this->zmm28,      other.zmm28,      sizeof(this->zmm28));
        std::memcpy(this->zmm29,      other.zmm29,      sizeof(this->zmm29));
        std::memcpy(this->zmm30,      other.zmm30,      sizeof(this->zmm30));
        std::memcpy(this->zmm31,      other.zmm31,      sizeof(this->zmm31));
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


      void x8664Cpu::clear(void) {
        /* Clear memory */
        this->memory.clear();

        /* Clear registers */
        std::memset(this->rax,        0x00, sizeof(this->rax));
        std::memset(this->rbx,        0x00, sizeof(this->rbx));
        std::memset(this->rcx,        0x00, sizeof(this->rcx));
        std::memset(this->rdx,        0x00, sizeof(this->rdx));
        std::memset(this->rdi,        0x00, sizeof(this->rdi));
        std::memset(this->rsi,        0x00, sizeof(this->rsi));
        std::memset(this->rsp,        0x00, sizeof(this->rsp));
        std::memset(this->rbp,        0x00, sizeof(this->rbp));
        std::memset(this->rip,        0x00, sizeof(this->rip));
        std::memset(this->eflags,     0x00, sizeof(this->eflags));
        std::memset(this->r8,         0x00, sizeof(this->r8));
        std::memset(this->r9,         0x00, sizeof(this->r9));
        std::memset(this->r10,        0x00, sizeof(this->r10));
        std::memset(this->r11,        0x00, sizeof(this->r11));
        std::memset(this->r12,        0x00, sizeof(this->r12));
        std::memset(this->r13,        0x00, sizeof(this->r13));
        std::memset(this->r14,        0x00, sizeof(this->r14));
        std::memset(this->r15,        0x00, sizeof(this->r15));
        std::memset(this->mm0,        0x00, sizeof(this->mm0));
        std::memset(this->mm1,        0x00, sizeof(this->mm1));
        std::memset(this->mm2,        0x00, sizeof(this->mm2));
        std::memset(this->mm3,        0x00, sizeof(this->mm3));
        std::memset(this->mm4,        0x00, sizeof(this->mm4));
        std::memset(this->mm5,        0x00, sizeof(this->mm5));
        std::memset(this->mm6,        0x00, sizeof(this->mm6));
        std::memset(this->mm7,        0x00, sizeof(this->mm7));
        std::memset(this->zmm0,       0x00, sizeof(this->zmm0));
        std::memset(this->zmm1,       0x00, sizeof(this->zmm1));
        std::memset(this->zmm2,       0x00, sizeof(this->zmm2));
        std::memset(this->zmm3,       0x00, sizeof(this->zmm3));
        std::memset(this->zmm4,       0x00, sizeof(this->zmm4));
        std::memset(this->zmm5,       0x00, sizeof(this->zmm5));
        std::memset(this->zmm6,       0x00, sizeof(this->zmm6));
        std::memset(this->zmm7,       0x00, sizeof(this->zmm7));
        std::memset(this->zmm8,       0x00, sizeof(this->zmm8));
        std::memset(this->zmm9,       0x00, sizeof(this->zmm9));
        std::memset(this->zmm10,      0x00, sizeof(this->zmm10));
        std::memset(this->zmm11,      0x00, sizeof(this->zmm11));
        std::memset(this->zmm12,      0x00, sizeof(this->zmm12));
        std::memset(this->zmm13,      0x00, sizeof(this->zmm13));
        std::memset(this->zmm14,      0x00, sizeof(this->zmm14));
        std::memset(this->zmm15,      0x00, sizeof(this->zmm15));
        std::memset(this->zmm16,      0x00, sizeof(this->zmm16));
        std::memset(this->zmm17,      0x00, sizeof(this->zmm17));
        std::memset(this->zmm18,      0x00, sizeof(this->zmm18));
        std::memset(this->zmm19,      0x00, sizeof(this->zmm19));
        std::memset(this->zmm20,      0x00, sizeof(this->zmm20));
        std::memset(this->zmm21,      0x00, sizeof(this->zmm21));
        std::memset(this->zmm22,      0x00, sizeof(this->zmm22));
        std::memset(this->zmm23,      0x00, sizeof(this->zmm23));
        std::memset(this->zmm24,      0x00, sizeof(this->zmm24));
        std::memset(this->zmm25,      0x00, sizeof(this->zmm25));
        std::memset(this->zmm26,      0x00, sizeof(this->zmm26));
        std::memset(this->zmm27,      0x00, sizeof(this->zmm27));
        std::memset(this->zmm28,      0x00, sizeof(this->zmm28));
        std::memset(this->zmm29,      0x00, sizeof(this->zmm29));
        std::memset(this->zmm30,      0x00, sizeof(this->zmm30));
        std::memset(this->zmm31,      0x00, sizeof(this->zmm31));
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


      x8664Cpu& x8664Cpu::operator=(const x8664Cpu& other) {
        this->copy(other);
        return *this;
      }


      triton::arch::endianness_e x8664Cpu::getEndianness(void) const {
        return triton::arch::LE_ENDIANNESS;
      }


      bool x8664Cpu::isFlag(triton::arch::register_e regId) const {
        if (regId >= triton::arch::ID_REG_X86_AC && regId <= triton::arch::ID_REG_X86_FSW_B) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FTW && regId <= triton::arch::ID_REG_X86_FDP) { return true; }
        if (regId >= triton::arch::ID_REG_X86_SSE_IE && regId <= triton::arch::ID_REG_X86_SSE_FZ) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FCW_IM && regId <= triton::arch::ID_REG_X86_FCW_X) { return true; }
        if (regId >= triton::arch::ID_REG_X86_FSW_IE && regId <= triton::arch::ID_REG_X86_FSW_B) { return true; }
        if (regId >= triton::arch::ID_REG_X86_EFER_TCE && regId <= triton::arch::ID_REG_X86_EFER_SCE) { return true; }
        return false;
      }


      bool x8664Cpu::isRegister(triton::arch::register_e regId) const {
        return (
          this->isGPR(regId)      ||
          this->isMMX(regId)      ||
          this->isSSE(regId)      ||
          this->isFPU(regId)      ||
          this->isEFER(regId)     ||
          this->isAVX256(regId)   ||
          this->isAVX512(regId)   ||
          this->isControl(regId)  ||
          this->isDebug(regId)    ||
          this->isSegment(regId)
        );
      }


      bool x8664Cpu::isRegisterValid(triton::arch::register_e regId) const {
        return (this->isFlag(regId) || this->isRegister(regId));
      }


      bool x8664Cpu::isGPR(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_RAX && regId <= triton::arch::ID_REG_X86_EFLAGS) ? true : false);
      }


      bool x8664Cpu::isMMX(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MM0 && regId <= triton::arch::ID_REG_X86_MM7) ? true : false);
      }


      bool x8664Cpu::isSSE(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_MXCSR && regId <= triton::arch::ID_REG_X86_XMM15) ? true : false);
      }


      bool x8664Cpu::isFPU(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_FTW && regId <= triton::arch::ID_REG_X86_FDP) ? true : false);
      }


      bool x8664Cpu::isEFER(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_EFER && regId <= triton::arch::ID_REG_X86_EFER) ? true : false);
      }


      bool x8664Cpu::isAVX256(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_YMM0 && regId <= triton::arch::ID_REG_X86_YMM15) ? true : false);
      }


      bool x8664Cpu::isAVX512(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_ZMM0 && regId <= triton::arch::ID_REG_X86_ZMM31) ? true : false);
      }


      bool x8664Cpu::isControl(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CR0 && regId <= triton::arch::ID_REG_X86_CR15) ? true : false);
      }


      bool x8664Cpu::isDebug(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_DR0 && regId <= triton::arch::ID_REG_X86_DR7) ? true : false);
      }


      bool x8664Cpu::isSegment(triton::arch::register_e regId) const {
        return ((regId >= triton::arch::ID_REG_X86_CS && regId <= triton::arch::ID_REG_X86_SS) ? true : false);
      }


      triton::uint32 x8664Cpu::numberOfRegisters(void) const {
        return triton::arch::ID_REG_LAST_ITEM;
      }


      triton::uint32 x8664Cpu::gprSize(void) const {
        return triton::size::qword;
      }


      triton::uint32 x8664Cpu::gprBitSize(void) const {
        return triton::bitsize::qword;
      }


      const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& x8664Cpu::getAllRegisters(void) const {
        return this->registers_;
      }


      std::set<const triton::arch::Register*> x8664Cpu::getParentRegisters(void) const {
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

          /* Add AVX-512 */
          else if (this->isAVX512(regId))
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


      const triton::arch::Register& x8664Cpu::getRegister(triton::arch::register_e id) const {
        try {
          return this->registers_.at(id);
        } catch (const std::out_of_range&) {
          throw triton::exceptions::Cpu("x8664Cpu::getRegister(): Invalid register for this architecture.");
        }
      }


      const triton::arch::Register& x8664Cpu::getParentRegister(const triton::arch::Register& reg) const {
        return this->getRegister(reg.getParent());
      }


      const triton::arch::Register& x8664Cpu::getParentRegister(triton::arch::register_e id) const {
        return this->getParentRegister(this->getRegister(id));
      }


      const triton::arch::Register& x8664Cpu::getProgramCounter(void) const {
        return this->getRegister(this->pcId);
      }


      const triton::arch::Register& x8664Cpu::getStackPointer(void) const {
        return this->getRegister(this->spId);
      }


      void x8664Cpu::disassembly(triton::arch::Instruction& inst) const {
        triton::extlibs::capstone::cs_insn* insn;
        triton::usize count = 0;

        /* Check if the opcode and opcode' size are defined */
        if (inst.getOpcode() == nullptr || inst.getSize() == 0)
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Opcode and opcodeSize must be definied.");

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

                triton::uint32 immsize = (this->isRegisterValid(base.getId()) ? base.getSize() :
                                          this->isRegisterValid(index.getId()) ? index.getSize() :
                                          this->gprSize());

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
                throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Invalid operand.");
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

          /* Free capstone stuffs */
          triton::extlibs::capstone::cs_free(insn, count);
        }
        else
          throw triton::exceptions::Disassembly("x8664Cpu::disassembly(): Failed to disassemble the given code.");
      }


      triton::uint8 x8664Cpu::getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks) const {
        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte));

        auto it = this->memory.find(addr);
        if (it == this->memory.end())
          return 0x00;

        return it->second;
      }


      triton::uint512 x8664Cpu::getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks) const {
        triton::uint512 ret = 0;
        triton::uint64 addr = 0;
        triton::uint32 size = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_MEMORY_VALUE, mem);

        addr = mem.getAddress();
        size = mem.getSize();

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x8664Cpu::getConcreteMemoryValue(): Invalid size memory.");

        for (triton::sint32 i = size-1; i >= 0; i--)
          ret = ((ret << triton::bitsize::byte) | this->getConcreteMemoryValue(addr+i, false));

        return ret;
      }


      std::vector<triton::uint8> x8664Cpu::getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks) const {
        std::vector<triton::uint8> area;

        for (triton::usize index = 0; index < size; index++)
          area.push_back(this->getConcreteMemoryValue(baseAddr+index));

        return area;
      }


      triton::uint512 x8664Cpu::getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks) const {
        triton::uint512 value = 0;

        if (execCallbacks && this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::GET_CONCRETE_REGISTER_VALUE, reg);

        switch (reg.getId()) {

          GRP_READ_2(A, rax);
          GRP_READ_2(B, rbx);
          GRP_READ_2(C, rcx);
          GRP_READ_2(D, rdx);

          GRP_READ_3(DI, rdi)
          GRP_READ_3(SI, rsi)
          GRP_READ_3(SP, rsp)
          GRP_READ_3(BP, rbp)

          GRP_READ_4(IP, rip)

          GR_READ(EFLAGS, eflags, uint64)

          GRP_READ_1(R8, r8)
          GRP_READ_1(R9, r9)
          GRP_READ_1(R10, r10)
          GRP_READ_1(R11, r11)
          GRP_READ_1(R12, r12)
          GRP_READ_1(R13, r13)
          GRP_READ_1(R14, r14)
          GRP_READ_1(R15, r15)

          MMX_READ(0, mm0)
          MMX_READ(1, mm1)
          MMX_READ(2, mm2)
          MMX_READ(3, mm3)
          MMX_READ(4, mm4)
          MMX_READ(5, mm5)
          MMX_READ(6, mm6)
          MMX_READ(7, mm7)

          XMM_READ(0, zmm0)
          XMM_READ(1, zmm1)
          XMM_READ(2, zmm2)
          XMM_READ(3, zmm3)
          XMM_READ(4, zmm4)
          XMM_READ(5, zmm5)
          XMM_READ(6, zmm6)
          XMM_READ(7, zmm7)
          XMM_READ(8, zmm8)
          XMM_READ(9, zmm9)
          XMM_READ(10, zmm10)
          XMM_READ(11, zmm11)
          XMM_READ(12, zmm12)
          XMM_READ(13, zmm13)
          XMM_READ(14, zmm14)
          XMM_READ(15, zmm15)

          YMM_READ(0, zmm0)
          YMM_READ(1, zmm1)
          YMM_READ(2, zmm2)
          YMM_READ(3, zmm3)
          YMM_READ(4, zmm4)
          YMM_READ(5, zmm5)
          YMM_READ(6, zmm6)
          YMM_READ(7, zmm7)
          YMM_READ(8, zmm8)
          YMM_READ(9, zmm9)
          YMM_READ(10, zmm10)
          YMM_READ(11, zmm11)
          YMM_READ(12, zmm12)
          YMM_READ(13, zmm13)
          YMM_READ(14, zmm14)
          YMM_READ(15, zmm15)

          ZMM_READ(0, zmm0)
          ZMM_READ(1, zmm1)
          ZMM_READ(2, zmm2)
          ZMM_READ(3, zmm3)
          ZMM_READ(4, zmm4)
          ZMM_READ(5, zmm5)
          ZMM_READ(6, zmm6)
          ZMM_READ(7, zmm7)
          ZMM_READ(8, zmm8)
          ZMM_READ(9, zmm9)
          ZMM_READ(10, zmm10)
          ZMM_READ(11, zmm11)
          ZMM_READ(12, zmm12)
          ZMM_READ(13, zmm13)
          ZMM_READ(14, zmm14)
          ZMM_READ(15, zmm15)
          ZMM_READ(16, zmm16)
          ZMM_READ(17, zmm17)
          ZMM_READ(18, zmm18)
          ZMM_READ(19, zmm19)
          ZMM_READ(20, zmm20)
          ZMM_READ(21, zmm21)
          ZMM_READ(22, zmm22)
          ZMM_READ(23, zmm23)
          ZMM_READ(24, zmm24)
          ZMM_READ(25, zmm25)
          ZMM_READ(26, zmm26)
          ZMM_READ(27, zmm27)
          ZMM_READ(28, zmm28)
          ZMM_READ(29, zmm29)
          ZMM_READ(30, zmm30)
          ZMM_READ(31, zmm31)

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

          FLG_READ(CF, eflags, uint64, 0)
          FLG_READ(PF, eflags, uint64, 2)
          FLG_READ(AF, eflags, uint64, 4)
          FLG_READ(ZF, eflags, uint64, 6)
          FLG_READ(SF, eflags, uint64, 7)
          FLG_READ(TF, eflags, uint64, 8)
          FLG_READ(IF, eflags, uint64, 9)
          FLG_READ(DF, eflags, uint64, 10)
          FLG_READ(OF, eflags, uint64, 11)
          FLG_READ(NT, eflags, uint64, 14)
          FLG_READ(RF, eflags, uint64, 16)
          FLG_READ(VM, eflags, uint64, 17)
          FLG_READ(AC, eflags, uint64, 18)
          FLG_READ(VIF, eflags, uint64, 19)
          FLG_READ(VIP, eflags, uint64, 20)
          FLG_READ(ID, eflags, uint64, 21)

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
            throw triton::exceptions::Cpu("x8664Cpu::getConcreteRegisterValue(): Invalid register.");
        }

        return value;
      }


      void x8664Cpu::setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) {
        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, MemoryAccess(addr, triton::size::byte), value);
        this->memory[addr] = value;
      }


      void x8664Cpu::setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();
        triton::uint512 cv  = value;

        if (cv > mem.getMaxValue())
          throw triton::exceptions::Register("x8664Cpu::setConcreteMemoryValue(): You cannot set this concrete value (too big) to this memory access.");

        if (size == 0 || size > triton::size::dqqword)
          throw triton::exceptions::Cpu("x8664Cpu::setConcreteMemoryValue(): Invalid size memory.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_MEMORY_VALUE, mem, value);

        for (triton::uint32 i = 0; i < size; i++) {
          this->memory[addr+i] = (cv & 0xff).convert_to<triton::uint8>();
          cv >>= 8;
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) {
        for (triton::usize index = 0; index < values.size(); index++) {
          this->setConcreteMemoryValue(baseAddr+index, values[index]);
        }
      }


      void x8664Cpu::setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          this->setConcreteMemoryValue(baseAddr+index, area[index]);
        }
      }


      void x8664Cpu::setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value) {
        if (value > reg.getMaxValue())
          throw triton::exceptions::Register("x8664Cpu::setConcreteRegisterValue(): You cannot set this concrete value (too big) to this register.");

        if (this->callbacks)
          this->callbacks->processCallbacks(triton::callbacks::SET_CONCRETE_REGISTER_VALUE, reg, value);

        switch (reg.getId()) {

          GRP_WRITE_2(A, rax)
          GRP_WRITE_2(B, rbx)
          GRP_WRITE_2(C, rcx)
          GRP_WRITE_2(D, rdx)

          GRP_WRITE_3(DI, rdi)
          GRP_WRITE_3(SI, rsi)
          GRP_WRITE_3(SP, rsp)
          GRP_WRITE_3(BP, rbp)

          GRP_WRITE_4(IP, rip)

          GR_WRITE(EFLAGS, eflags, uint64)

          FLG_WRITE(CF, eflags, uint64, 0)
          FLG_WRITE(PF, eflags, uint64, 2)
          FLG_WRITE(AF, eflags, uint64, 4)
          FLG_WRITE(ZF, eflags, uint64, 6)
          FLG_WRITE(SF, eflags, uint64, 7)
          FLG_WRITE(TF, eflags, uint64, 8)
          FLG_WRITE(IF, eflags, uint64, 9)
          FLG_WRITE(DF, eflags, uint64, 10)
          FLG_WRITE(OF, eflags, uint64, 11)
          FLG_WRITE(NT, eflags, uint64, 14)
          FLG_WRITE(RF, eflags, uint64, 16)
          FLG_WRITE(VM, eflags, uint64, 17)
          FLG_WRITE(AC, eflags, uint64, 18)
          FLG_WRITE(VIF, eflags, uint64, 19)
          FLG_WRITE(VIP, eflags, uint64, 20)
          FLG_WRITE(ID, eflags, uint64, 21)

          GRP_WRITE_1(R8, r8)
          GRP_WRITE_1(R9, r9)
          GRP_WRITE_1(R10, r10)
          GRP_WRITE_1(R11, r11)
          GRP_WRITE_1(R12, r12)
          GRP_WRITE_1(R13, r13)
          GRP_WRITE_1(R14, r14)
          GRP_WRITE_1(R15, r15)

          MMX_WRITE(0, mm0)
          MMX_WRITE(1, mm1)
          MMX_WRITE(2, mm2)
          MMX_WRITE(3, mm3)
          MMX_WRITE(4, mm4)
          MMX_WRITE(5, mm5)
          MMX_WRITE(6, mm6)
          MMX_WRITE(7, mm7)

          XMM_WRITE(0, zmm0)
          XMM_WRITE(1, zmm1)
          XMM_WRITE(2, zmm2)
          XMM_WRITE(3, zmm3)
          XMM_WRITE(4, zmm4)
          XMM_WRITE(5, zmm5)
          XMM_WRITE(6, zmm6)
          XMM_WRITE(7, zmm7)
          XMM_WRITE(8, zmm8)
          XMM_WRITE(9, zmm9)
          XMM_WRITE(10, zmm10)
          XMM_WRITE(11, zmm11)
          XMM_WRITE(12, zmm12)
          XMM_WRITE(13, zmm13)
          XMM_WRITE(14, zmm14)
          XMM_WRITE(15, zmm15)

          YMM_WRITE(0, zmm0)
          YMM_WRITE(1, zmm1)
          YMM_WRITE(2, zmm2)
          YMM_WRITE(3, zmm3)
          YMM_WRITE(4, zmm4)
          YMM_WRITE(5, zmm5)
          YMM_WRITE(6, zmm6)
          YMM_WRITE(7, zmm7)
          YMM_WRITE(8, zmm8)
          YMM_WRITE(9, zmm9)
          YMM_WRITE(10, zmm10)
          YMM_WRITE(11, zmm11)
          YMM_WRITE(12, zmm12)
          YMM_WRITE(13, zmm13)
          YMM_WRITE(14, zmm14)
          YMM_WRITE(15, zmm15)

          ZMM_WRITE(0, zmm0)
          ZMM_WRITE(1, zmm1)
          ZMM_WRITE(2, zmm2)
          ZMM_WRITE(3, zmm3)
          ZMM_WRITE(4, zmm4)
          ZMM_WRITE(5, zmm5)
          ZMM_WRITE(6, zmm6)
          ZMM_WRITE(7, zmm7)
          ZMM_WRITE(8, zmm8)
          ZMM_WRITE(9, zmm9)
          ZMM_WRITE(10, zmm10)
          ZMM_WRITE(11, zmm11)
          ZMM_WRITE(12, zmm12)
          ZMM_WRITE(13, zmm13)
          ZMM_WRITE(14, zmm14)
          ZMM_WRITE(15, zmm15)
          ZMM_WRITE(16, zmm16)
          ZMM_WRITE(17, zmm17)
          ZMM_WRITE(18, zmm18)
          ZMM_WRITE(19, zmm19)
          ZMM_WRITE(20, zmm20)
          ZMM_WRITE(21, zmm21)
          ZMM_WRITE(22, zmm22)
          ZMM_WRITE(23, zmm23)
          ZMM_WRITE(24, zmm24)
          ZMM_WRITE(25, zmm25)
          ZMM_WRITE(26, zmm26)
          ZMM_WRITE(27, zmm27)
          ZMM_WRITE(28, zmm28)
          ZMM_WRITE(29, zmm29)
          ZMM_WRITE(30, zmm30)
          ZMM_WRITE(31, zmm31)

          GR_WRITE(MXCSR, mxcsr, uint32)
          GR_WRITE(MXCSR_MASK, mxcsr_mask, uint32)

          FLG_WRITE(SSE_IE, mxcsr, uint32, 0)
          FLG_WRITE(SSE_DE, mxcsr, uint32, 1)
          FLG_WRITE(SSE_ZE, mxcsr, uint32, 2)
          FLG_WRITE(SSE_OE, mxcsr, uint32, 3)
          FLG_WRITE(SSE_UE, mxcsr, uint32, 4)
          FLG_WRITE(SSE_PE, mxcsr, uint32, 5)
          FLG_WRITE(SSE_DAZ, mxcsr, uint32, 6)
          FLG_WRITE(SSE_IM, mxcsr, uint32, 7)
          FLG_WRITE(SSE_DM, mxcsr, uint32, 8)
          FLG_WRITE(SSE_ZM, mxcsr, uint32, 9)
          FLG_WRITE(SSE_OM, mxcsr, uint32, 10)
          FLG_WRITE(SSE_UM, mxcsr, uint32, 11)
          FLG_WRITE(SSE_PM, mxcsr, uint32, 12)
          FLG_WRITE(SSE_RL, mxcsr, uint32, 13)
          FLG_WRITE(SSE_RH, mxcsr, uint32, 14)
          FLG_WRITE(SSE_FZ, mxcsr, uint32, 15)

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
          FLG_WRITE(FCW_X, fcw, uint16, 12)

          FLG_WRITE(FSW_IE, fsw, uint16, 0)
          FLG_WRITE(FSW_DE, fsw, uint16, 1)
          FLG_WRITE(FSW_ZE, fsw, uint16, 2)
          FLG_WRITE(FSW_OE, fsw, uint16, 3)
          FLG_WRITE(FSW_UE, fsw, uint16, 4)
          FLG_WRITE(FSW_PE, fsw, uint16, 5)
          FLG_WRITE(FSW_SF, fsw, uint16, 6)
          FLG_WRITE(FSW_ES, fsw, uint16, 7)
          FLG_WRITE(FSW_C0, fsw, uint16, 8)
          FLG_WRITE(FSW_C1, fsw, uint16, 9)
          FLG_WRITE(FSW_C2, fsw, uint16, 10)
          FLG_WRITE(FSW_TOP, fsw, uint16, 11)
          FLG_WRITE(FSW_C3, fsw, uint16, 14)
          FLG_WRITE(FSW_B, fsw, uint16, 15)

          GR_WRITE(EFER, efer, uint64)

          FLG_WRITE(EFER_SCE, efer, uint64, 0)
          FLG_WRITE(EFER_LME, efer, uint64, 8)
          FLG_WRITE(EFER_LMA, efer, uint64, 10)
          FLG_WRITE(EFER_NXE, efer, uint64, 11)
          FLG_WRITE(EFER_SVME, efer, uint64, 12)
          FLG_WRITE(EFER_LMSLE, efer, uint64, 13)
          FLG_WRITE(EFER_FFXSR, efer, uint64, 14)
          FLG_WRITE(EFER_TCE, efer, uint64, 15)

          CRR_WRITE(0, cr0)
          CRR_WRITE(1, cr1)
          CRR_WRITE(2, cr2)
          CRR_WRITE(3, cr3)
          CRR_WRITE(4, cr4)
          CRR_WRITE(5, cr5)
          CRR_WRITE(6, cr6)
          CRR_WRITE(7, cr7)
          CRR_WRITE(8, cr8)
          CRR_WRITE(9, cr9)
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

          SEG_WRITE(CS, cs)
          SEG_WRITE(DS, ds)
          SEG_WRITE(ES, es)
          SEG_WRITE(FS, fs)
          SEG_WRITE(GS, gs)
          SEG_WRITE(SS, ss)

          default:
            throw triton::exceptions::Cpu("x8664Cpu:setConcreteRegisterValue(): Invalid register.");
        }
      }


      bool x8664Cpu::isThumb(void) const {
        /* There is no thumb mode in x86_64 */
        return false;
      }


      void x8664Cpu::setThumb(bool state) {
        /* There is no thumb mode in x86_64 */
      }


      bool x8664Cpu::isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const {
        return this->isConcreteMemoryValueDefined(mem.getAddress(), mem.getSize());
      }


      bool x8664Cpu::isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size) const {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) == this->memory.end())
            return false;
        }
        return true;
      }


      void x8664Cpu::clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem) {
        this->clearConcreteMemoryValue(mem.getAddress(), mem.getSize());
      }


      void x8664Cpu::clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size) {
        for (triton::usize index = 0; index < size; index++) {
          if (this->memory.find(baseAddr + index) != this->memory.end()) {
            this->memory.erase(baseAddr + index);
          }
        }
      }

    }; /* x86 namespace */
  }; /* arch namespace */
}; /* triton namespace */
