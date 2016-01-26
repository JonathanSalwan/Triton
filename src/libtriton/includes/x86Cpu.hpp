//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_X86CPU_HPP
#define TRITON_X86CPU_HPP

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

      //! \class x86Cpu
      /*! \brief This class is used to describe the x86 (32-bits) spec. */
      class x86Cpu : public AbstractCpu {

        protected:

          /*! \brief map of address -> concrete value
           *
           * \description
           * **item1**: memory address<br>
           * **item2**: concrete value
           */
          std::map<triton::__uint, triton::uint8> memory;

          //! Concrete value of eax
          triton::uint8 eax[DWORD_SIZE];
          //! Concrete value of ebx
          triton::uint8 ebx[DWORD_SIZE];
          //! Concrete value of ecx
          triton::uint8 ecx[DWORD_SIZE];
          //! Concrete value of edx
          triton::uint8 edx[DWORD_SIZE];
          //! Concrete value of edi
          triton::uint8 edi[DWORD_SIZE];
          //! Concrete value of esi
          triton::uint8 esi[DWORD_SIZE];
          //! Concrete value of ebp
          triton::uint8 ebp[DWORD_SIZE];
          //! Concrete value of esp
          triton::uint8 esp[DWORD_SIZE];
          //! Concrete value of eip
          triton::uint8 eip[DWORD_SIZE];
          //! Concrete value of eflags
          triton::uint8 eflags[DWORD_SIZE];
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


        public:
          x86Cpu();
          //! Constructor by copy.
          x86Cpu(const x86Cpu& other);
          ~x86Cpu();

          //! Copies a x86Cpu class.
          void copy(const x86Cpu& other);

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

          //! Copies a x86Cpu class.
          void operator=(const x86Cpu& other);
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};


#endif  /* !X86CPU_HPP */
