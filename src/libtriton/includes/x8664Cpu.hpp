//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_X8664CPU_HPP
#define TRITON_X8664CPU_HPP

#include <map>
#include <set>
#include <tuple>

#include "abstractCpu.hpp"
#include "instruction.hpp"
#include "memoryOperand.hpp"
#include "registerOperand.hpp"
#include "tritonTypes.hpp"
#include "x86Semantics.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! \module The x86 namespace
    namespace x86 {
    /*!
     *  \ingroup arch
     *  \addtogroup x86
     *  @{
     */

      //! \class x8664Cpu
      /*! \brief This class is used to describe the x86 (64-bits) spec. */
      class x8664Cpu : public AbstractCpu {

        protected:

          /*! \brief map of address -> concrete value
           *
           * \description
           * **item1**: memory address<br>
           * **item2**: concrete value
           */
          std::map<triton::__uint, triton::uint8> memory;

          //! Concrete value of rax
          triton::uint8 rax[QWORD_SIZE];
          //! Concrete value of rbx
          triton::uint8 rbx[QWORD_SIZE];
          //! Concrete value of rcx
          triton::uint8 rcx[QWORD_SIZE];
          //! Concrete value of rdx
          triton::uint8 rdx[QWORD_SIZE];
          //! Concrete value of rdi
          triton::uint8 rdi[QWORD_SIZE];
          //! Concrete value of rsi
          triton::uint8 rsi[QWORD_SIZE];
          //! Concrete value of rbp
          triton::uint8 rbp[QWORD_SIZE];
          //! Concrete value of rsp
          triton::uint8 rsp[QWORD_SIZE];
          //! Concrete value of rip
          triton::uint8 rip[QWORD_SIZE];
          //! Concrete value of r8
          triton::uint8 r8[QWORD_SIZE];
          //! Concrete value of r9
          triton::uint8 r9[QWORD_SIZE];
          //! Concrete value of r10
          triton::uint8 r10[QWORD_SIZE];
          //! Concrete value of r11
          triton::uint8 r11[QWORD_SIZE];
          //! Concrete value of r12
          triton::uint8 r12[QWORD_SIZE];
          //! Concrete value of r13
          triton::uint8 r13[QWORD_SIZE];
          //! Concrete value of r14
          triton::uint8 r14[QWORD_SIZE];
          //! Concrete value of r15
          triton::uint8 r15[QWORD_SIZE];
          //! Concrete value of rflags
          triton::uint8 rflags[QWORD_SIZE];
          //! Concrete value of xmm0
          triton::uint8 xmm0[DQWORD_SIZE];
          //! Concrete value of xmm1
          triton::uint8 xmm1[DQWORD_SIZE];
          //! Concrete value of xmm2
          triton::uint8 xmm2[DQWORD_SIZE];
          //! Concrete value of xmm3
          triton::uint8 xmm3[DQWORD_SIZE];
          //! Concrete value of xmm4
          triton::uint8 xmm4[DQWORD_SIZE];
          //! Concrete value of xmm5
          triton::uint8 xmm5[DQWORD_SIZE];
          //! Concrete value of xmm6
          triton::uint8 xmm6[DQWORD_SIZE];
          //! Concrete value of xmm7
          triton::uint8 xmm7[DQWORD_SIZE];
          //! Concrete value of xmm8
          triton::uint8 xmm8[DQWORD_SIZE];
          //! Concrete value of xmm9
          triton::uint8 xmm9[DQWORD_SIZE];
          //! Concrete value of xmm10
          triton::uint8 xmm10[DQWORD_SIZE];
          //! Concrete value of xmm11
          triton::uint8 xmm11[DQWORD_SIZE];
          //! Concrete value of xmm12
          triton::uint8 xmm12[DQWORD_SIZE];
          //! Concrete value of xmm13
          triton::uint8 xmm13[DQWORD_SIZE];
          //! Concrete value of xmm14
          triton::uint8 xmm14[DQWORD_SIZE];
          //! Concrete value of xmm15
          triton::uint8 xmm15[DQWORD_SIZE];


        public:
          x8664Cpu();
          //! Constructor by copy.
          x8664Cpu(const x8664Cpu& other);
          ~x8664Cpu();

          //! Copies a x8664Cpu class.
          void copy(const x8664Cpu& other);

          void init(void);
          void clear(void);
          bool isFlag(triton::uint32 regId);
          bool isReg(triton::uint32 regId);
          bool isRegValid(triton::uint32 regId);

          //! Returns true if regId is a GRP.
          bool isGPR(triton::uint32 regId);

          //! Returns true if regId is a SSE register.
          bool isSSE(triton::uint32 regId);

          std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> getRegInfo(triton::uint32 reg);
          std::set<triton::arch::RegisterOperand*> getParentRegisters(void);
          triton::uint128 getLastMemoryValue(triton::arch::MemoryOperand& mem);
          triton::uint128 getLastRegisterValue(triton::arch::RegisterOperand& reg);
          triton::uint32 invalidReg(void);
          triton::uint32 numberOfReg(void);
          triton::uint32 regBitSize(void);
          triton::uint32 regSize(void);
          triton::uint8 getLastMemoryValue(triton::__uint addr);
          void buildSemantics(triton::arch::Instruction &inst);
          void disassembly(triton::arch::Instruction &inst);
          void setLastMemoryValue(triton::__uint addr, triton::uint8 value);
          void setLastMemoryValue(triton::arch::MemoryOperand& mem);
          void setLastRegisterValue(triton::arch::RegisterOperand& reg);

          //! Copies a x8664Cpu class.
          void operator=(const x8664Cpu& other);
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif  /* !X86CPU_HPP */
