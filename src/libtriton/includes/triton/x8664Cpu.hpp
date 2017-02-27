//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_X8664CPU_HPP
#define TRITON_X8664CPU_HPP

#include <map>
#include <set>
#include <vector>

#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/registerSpecification.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/x86Specifications.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! The x86 namespace
    namespace x86 {
    /*!
     *  \ingroup arch
     *  \addtogroup x86
     *  @{
     */

      //! \class x8664Cpu
      /*! \brief This class is used to describe the x86 (64-bits) spec. */
      class x8664Cpu : public CpuInterface, public x86Specifications {
        private:
          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

        protected:
          /*! \brief map of address -> concrete value
           *
           * \description
           * **item1**: memory address<br>
           * **item2**: concrete value
           */
          std::map<triton::uint64, triton::uint8> memory;

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
          //! Concrete value of eflags
          triton::uint8 eflags[QWORD_SIZE];
          //! Concrete value of mm0
          triton::uint8 mm0[QWORD_SIZE];
          //! Concrete value of mm1
          triton::uint8 mm1[QWORD_SIZE];
          //! Concrete value of mm2
          triton::uint8 mm2[QWORD_SIZE];
          //! Concrete value of mm3
          triton::uint8 mm3[QWORD_SIZE];
          //! Concrete value of mm4
          triton::uint8 mm4[QWORD_SIZE];
          //! Concrete value of mm5
          triton::uint8 mm5[QWORD_SIZE];
          //! Concrete value of mm6
          triton::uint8 mm6[QWORD_SIZE];
          //! Concrete value of mm7
          triton::uint8 mm7[QWORD_SIZE];
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
          //! Concrete value of ymm0
          triton::uint8 ymm0[QQWORD_SIZE];
          //! Concrete value of ymm1
          triton::uint8 ymm1[QQWORD_SIZE];
          //! Concrete value of ymm2
          triton::uint8 ymm2[QQWORD_SIZE];
          //! Concrete value of ymm3
          triton::uint8 ymm3[QQWORD_SIZE];
          //! Concrete value of ymm4
          triton::uint8 ymm4[QQWORD_SIZE];
          //! Concrete value of ymm5
          triton::uint8 ymm5[QQWORD_SIZE];
          //! Concrete value of ymm6
          triton::uint8 ymm6[QQWORD_SIZE];
          //! Concrete value of ymm7
          triton::uint8 ymm7[QQWORD_SIZE];
          //! Concrete value of ymm8
          triton::uint8 ymm8[QQWORD_SIZE];
          //! Concrete value of ymm9
          triton::uint8 ymm9[QQWORD_SIZE];
          //! Concrete value of ymm10
          triton::uint8 ymm10[QQWORD_SIZE];
          //! Concrete value of ymm11
          triton::uint8 ymm11[QQWORD_SIZE];
          //! Concrete value of ymm12
          triton::uint8 ymm12[QQWORD_SIZE];
          //! Concrete value of ymm13
          triton::uint8 ymm13[QQWORD_SIZE];
          //! Concrete value of ymm14
          triton::uint8 ymm14[QQWORD_SIZE];
          //! Concrete value of ymm15
          triton::uint8 ymm15[QQWORD_SIZE];
          //! Concrete value of zmm0
          triton::uint8 zmm0[DQQWORD_SIZE];
          //! Concrete value of zmm1
          triton::uint8 zmm1[DQQWORD_SIZE];
          //! Concrete value of zmm2
          triton::uint8 zmm2[DQQWORD_SIZE];
          //! Concrete value of zmm3
          triton::uint8 zmm3[DQQWORD_SIZE];
          //! Concrete value of zmm4
          triton::uint8 zmm4[DQQWORD_SIZE];
          //! Concrete value of zmm5
          triton::uint8 zmm5[DQQWORD_SIZE];
          //! Concrete value of zmm6
          triton::uint8 zmm6[DQQWORD_SIZE];
          //! Concrete value of zmm7
          triton::uint8 zmm7[DQQWORD_SIZE];
          //! Concrete value of zmm8
          triton::uint8 zmm8[DQQWORD_SIZE];
          //! Concrete value of zmm9
          triton::uint8 zmm9[DQQWORD_SIZE];
          //! Concrete value of zmm10
          triton::uint8 zmm10[DQQWORD_SIZE];
          //! Concrete value of zmm11
          triton::uint8 zmm11[DQQWORD_SIZE];
          //! Concrete value of zmm12
          triton::uint8 zmm12[DQQWORD_SIZE];
          //! Concrete value of zmm13
          triton::uint8 zmm13[DQQWORD_SIZE];
          //! Concrete value of zmm14
          triton::uint8 zmm14[DQQWORD_SIZE];
          //! Concrete value of zmm15
          triton::uint8 zmm15[DQQWORD_SIZE];
          //! Concrete value of zmm16
          triton::uint8 zmm16[DQQWORD_SIZE];
          //! Concrete value of zmm17
          triton::uint8 zmm17[DQQWORD_SIZE];
          //! Concrete value of zmm18
          triton::uint8 zmm18[DQQWORD_SIZE];
          //! Concrete value of zmm19
          triton::uint8 zmm19[DQQWORD_SIZE];
          //! Concrete value of zmm20
          triton::uint8 zmm20[DQQWORD_SIZE];
          //! Concrete value of zmm21
          triton::uint8 zmm21[DQQWORD_SIZE];
          //! Concrete value of zmm22
          triton::uint8 zmm22[DQQWORD_SIZE];
          //! Concrete value of zmm23
          triton::uint8 zmm23[DQQWORD_SIZE];
          //! Concrete value of zmm24
          triton::uint8 zmm24[DQQWORD_SIZE];
          //! Concrete value of zmm25
          triton::uint8 zmm25[DQQWORD_SIZE];
          //! Concrete value of zmm26
          triton::uint8 zmm26[DQQWORD_SIZE];
          //! Concrete value of zmm27
          triton::uint8 zmm27[DQQWORD_SIZE];
          //! Concrete value of zmm28
          triton::uint8 zmm28[DQQWORD_SIZE];
          //! Concrete value of zmm29
          triton::uint8 zmm29[DQQWORD_SIZE];
          //! Concrete value of zmm30
          triton::uint8 zmm30[DQQWORD_SIZE];
          //! Concrete value of zmm31
          triton::uint8 zmm31[DQQWORD_SIZE];
          //! Concrete value of mxcsr
          triton::uint8 mxcsr[QWORD_SIZE];
          //! Concrete value of cr0
          triton::uint8 cr0[QWORD_SIZE];
          //! Concrete value of cr1
          triton::uint8 cr1[QWORD_SIZE];
          //! Concrete value of cr2
          triton::uint8 cr2[QWORD_SIZE];
          //! Concrete value of cr3
          triton::uint8 cr3[QWORD_SIZE];
          //! Concrete value of cr4
          triton::uint8 cr4[QWORD_SIZE];
          //! Concrete value of cr5
          triton::uint8 cr5[QWORD_SIZE];
          //! Concrete value of cr6
          triton::uint8 cr6[QWORD_SIZE];
          //! Concrete value of cr7
          triton::uint8 cr7[QWORD_SIZE];
          //! Concrete value of cr8
          triton::uint8 cr8[QWORD_SIZE];
          //! Concrete value of cr9
          triton::uint8 cr9[QWORD_SIZE];
          //! Concrete value of cr10
          triton::uint8 cr10[QWORD_SIZE];
          //! Concrete value of cr11
          triton::uint8 cr11[QWORD_SIZE];
          //! Concrete value of cr12
          triton::uint8 cr12[QWORD_SIZE];
          //! Concrete value of cr13
          triton::uint8 cr13[QWORD_SIZE];
          //! Concrete value of cr14
          triton::uint8 cr14[QWORD_SIZE];
          //! Concrete value of cr15
          triton::uint8 cr15[QWORD_SIZE];
          //! Concrete value of CS
          triton::uint8 cs[QWORD_SIZE];
          //! Concrete value of DS
          triton::uint8 ds[QWORD_SIZE];
          //! Concrete value of ES
          triton::uint8 es[QWORD_SIZE];
          //! Concrete value of FS
          triton::uint8 fs[QWORD_SIZE];
          //! Concrete value of GS
          triton::uint8 gs[QWORD_SIZE];
          //! Concrete value of SS
          triton::uint8 ss[QWORD_SIZE];

        public:
          //! Constructor.
          x8664Cpu(triton::callbacks::Callbacks* callbacks=nullptr);

          //! Constructor by copy.
          x8664Cpu(const x8664Cpu& other);

          //! Destructor.
          virtual ~x8664Cpu();

          //! Copies a x8664Cpu class.
          void operator=(const x8664Cpu& other);

          //! Copies a x8664Cpu class.
          void copy(const x8664Cpu& other);

          //! Returns true if regId is a GRP.
          bool isGPR(triton::uint32 regId) const;

          //! Returns true if regId is a MMX register.
          bool isMMX(triton::uint32 regId) const;

          //! Returns true if regId is a SSE register.
          bool isSSE(triton::uint32 regId) const;

          //! Returns true if regId is a AVX-256 (YMM) register.
          bool isAVX256(triton::uint32 regId) const;

          //! Returns true if regId is a AVX-512 (ZMM) register.
          bool isAVX512(triton::uint32 regId) const;

          //! Returns true if regId is a control (cr) register.
          bool isControl(triton::uint32 regId) const;

          //! Returns true if regId is a Segment.
          bool isSegment(triton::uint32 regId) const;

          /* Virtual pure inheritance ================================================= */
          bool isFlag(triton::uint32 regId) const;
          bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);
          bool isRegister(triton::uint32 regId) const;
          bool isRegisterValid(triton::uint32 regId) const;
          std::set<triton::arch::Register*> getAllRegisters(void) const;
          std::set<triton::arch::Register*> getParentRegisters(void) const;
          std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;
          triton::arch::RegisterSpecification getRegisterSpecification(triton::uint32 regId) const;
          triton::uint32 numberOfRegisters(void) const;
          triton::uint32 registerBitSize(void) const;
          triton::uint32 registerSize(void) const;
          triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const;
          triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const;
          triton::uint8 getConcreteMemoryValue(triton::uint64 addr) const;
          void clear(void);
          void disassembly(triton::arch::Instruction& inst) const;
          void init(void);
          void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);
          void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);
          void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem);
          void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);
          void setConcreteRegisterValue(const triton::arch::Register& reg);
          void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);
          /* End of virtual pure inheritance ========================================== */
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif  /* !X86CPU_HPP */
