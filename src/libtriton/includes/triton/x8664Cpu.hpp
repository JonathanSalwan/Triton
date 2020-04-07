//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_X8664CPU_HPP
#define TRITON_X8664CPU_HPP

#include <set>
#include <unordered_map>
#include <vector>

#include <triton/archEnums.hpp>
#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/dllexport.hpp>
#include <triton/externalLibs.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
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

        static const triton::arch::register_e pcId = triton::arch::ID_REG_X86_RIP;
        static const triton::arch::register_e spId = triton::arch::ID_REG_X86_RSP;

        private:
          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

          //! Capstone context
          triton::extlibs::capstone::csh handle;

          //! Copies a x8664Cpu class.
          void copy(const x8664Cpu& other);

          //! Initializes the disassembler
          void disassInit(void);

        protected:
          /*! \brief map of address -> concrete value
           *
           * \details
           * **item1**: memory address<br>
           * **item2**: concrete value
           */
          std::unordered_map<triton::uint64, triton::uint8> memory;

          //! Concrete value of rax
          triton::uint8 rax[triton::size::qword];
          //! Concrete value of rbx
          triton::uint8 rbx[triton::size::qword];
          //! Concrete value of rcx
          triton::uint8 rcx[triton::size::qword];
          //! Concrete value of rdx
          triton::uint8 rdx[triton::size::qword];
          //! Concrete value of rdi
          triton::uint8 rdi[triton::size::qword];
          //! Concrete value of rsi
          triton::uint8 rsi[triton::size::qword];
          //! Concrete value of rbp
          triton::uint8 rbp[triton::size::qword];
          //! Concrete value of rsp
          triton::uint8 rsp[triton::size::qword];
          //! Concrete value of rip
          triton::uint8 rip[triton::size::qword];
          //! Concrete value of r8
          triton::uint8 r8[triton::size::qword];
          //! Concrete value of r9
          triton::uint8 r9[triton::size::qword];
          //! Concrete value of r10
          triton::uint8 r10[triton::size::qword];
          //! Concrete value of r11
          triton::uint8 r11[triton::size::qword];
          //! Concrete value of r12
          triton::uint8 r12[triton::size::qword];
          //! Concrete value of r13
          triton::uint8 r13[triton::size::qword];
          //! Concrete value of r14
          triton::uint8 r14[triton::size::qword];
          //! Concrete value of r15
          triton::uint8 r15[triton::size::qword];
          //! Concrete value of eflags
          triton::uint8 eflags[triton::size::qword];
          //! Concrete value of mm0
          triton::uint8 mm0[triton::size::qword];
          //! Concrete value of mm1
          triton::uint8 mm1[triton::size::qword];
          //! Concrete value of mm2
          triton::uint8 mm2[triton::size::qword];
          //! Concrete value of mm3
          triton::uint8 mm3[triton::size::qword];
          //! Concrete value of mm4
          triton::uint8 mm4[triton::size::qword];
          //! Concrete value of mm5
          triton::uint8 mm5[triton::size::qword];
          //! Concrete value of mm6
          triton::uint8 mm6[triton::size::qword];
          //! Concrete value of mm7
          triton::uint8 mm7[triton::size::qword];
          //! Concrete value of zmm0
          triton::uint8 zmm0[triton::size::dqqword];
          //! Concrete value of zmm1
          triton::uint8 zmm1[triton::size::dqqword];
          //! Concrete value of zmm2
          triton::uint8 zmm2[triton::size::dqqword];
          //! Concrete value of zmm3
          triton::uint8 zmm3[triton::size::dqqword];
          //! Concrete value of zmm4
          triton::uint8 zmm4[triton::size::dqqword];
          //! Concrete value of zmm5
          triton::uint8 zmm5[triton::size::dqqword];
          //! Concrete value of zmm6
          triton::uint8 zmm6[triton::size::dqqword];
          //! Concrete value of zmm7
          triton::uint8 zmm7[triton::size::dqqword];
          //! Concrete value of zmm8
          triton::uint8 zmm8[triton::size::dqqword];
          //! Concrete value of zmm9
          triton::uint8 zmm9[triton::size::dqqword];
          //! Concrete value of zmm10
          triton::uint8 zmm10[triton::size::dqqword];
          //! Concrete value of zmm11
          triton::uint8 zmm11[triton::size::dqqword];
          //! Concrete value of zmm12
          triton::uint8 zmm12[triton::size::dqqword];
          //! Concrete value of zmm13
          triton::uint8 zmm13[triton::size::dqqword];
          //! Concrete value of zmm14
          triton::uint8 zmm14[triton::size::dqqword];
          //! Concrete value of zmm15
          triton::uint8 zmm15[triton::size::dqqword];
          //! Concrete value of zmm16
          triton::uint8 zmm16[triton::size::dqqword];
          //! Concrete value of zmm17
          triton::uint8 zmm17[triton::size::dqqword];
          //! Concrete value of zmm18
          triton::uint8 zmm18[triton::size::dqqword];
          //! Concrete value of zmm19
          triton::uint8 zmm19[triton::size::dqqword];
          //! Concrete value of zmm20
          triton::uint8 zmm20[triton::size::dqqword];
          //! Concrete value of zmm21
          triton::uint8 zmm21[triton::size::dqqword];
          //! Concrete value of zmm22
          triton::uint8 zmm22[triton::size::dqqword];
          //! Concrete value of zmm23
          triton::uint8 zmm23[triton::size::dqqword];
          //! Concrete value of zmm24
          triton::uint8 zmm24[triton::size::dqqword];
          //! Concrete value of zmm25
          triton::uint8 zmm25[triton::size::dqqword];
          //! Concrete value of zmm26
          triton::uint8 zmm26[triton::size::dqqword];
          //! Concrete value of zmm27
          triton::uint8 zmm27[triton::size::dqqword];
          //! Concrete value of zmm28
          triton::uint8 zmm28[triton::size::dqqword];
          //! Concrete value of zmm29
          triton::uint8 zmm29[triton::size::dqqword];
          //! Concrete value of zmm30
          triton::uint8 zmm30[triton::size::dqqword];
          //! Concrete value of zmm31
          triton::uint8 zmm31[triton::size::dqqword];
          //! Concrete value of mxcsr
          triton::uint8 mxcsr[triton::size::qword];
          //! Concrete value of cr0
          triton::uint8 cr0[triton::size::qword];
          //! Concrete value of cr1
          triton::uint8 cr1[triton::size::qword];
          //! Concrete value of cr2
          triton::uint8 cr2[triton::size::qword];
          //! Concrete value of cr3
          triton::uint8 cr3[triton::size::qword];
          //! Concrete value of cr4
          triton::uint8 cr4[triton::size::qword];
          //! Concrete value of cr5
          triton::uint8 cr5[triton::size::qword];
          //! Concrete value of cr6
          triton::uint8 cr6[triton::size::qword];
          //! Concrete value of cr7
          triton::uint8 cr7[triton::size::qword];
          //! Concrete value of cr8
          triton::uint8 cr8[triton::size::qword];
          //! Concrete value of cr9
          triton::uint8 cr9[triton::size::qword];
          //! Concrete value of cr10
          triton::uint8 cr10[triton::size::qword];
          //! Concrete value of cr11
          triton::uint8 cr11[triton::size::qword];
          //! Concrete value of cr12
          triton::uint8 cr12[triton::size::qword];
          //! Concrete value of cr13
          triton::uint8 cr13[triton::size::qword];
          //! Concrete value of cr14
          triton::uint8 cr14[triton::size::qword];
          //! Concrete value of cr15
          triton::uint8 cr15[triton::size::qword];
          //! Concrete value of CS
          triton::uint8 cs[triton::size::qword];
          //! Concrete value of DS
          triton::uint8 ds[triton::size::qword];
          //! Concrete value of ES
          triton::uint8 es[triton::size::qword];
          //! Concrete value of FS
          triton::uint8 fs[triton::size::qword];
          //! Concrete value of GS
          triton::uint8 gs[triton::size::qword];
          //! Concrete value of SS
          triton::uint8 ss[triton::size::qword];
          //! Concrete value of dr0
          triton::uint8 dr0[triton::size::qword];
          //! Condete value of dr1
          triton::uint8 dr1[triton::size::qword];
          //! Condete value of dr2
          triton::uint8 dr2[triton::size::qword];
          //! Condete value of dr3
          triton::uint8 dr3[triton::size::qword];
          //! Condete value of dr6
          triton::uint8 dr6[triton::size::qword];
          //! Condete value of dr7
          triton::uint8 dr7[triton::size::qword];

        public:
          //! Constructor.
          TRITON_EXPORT x8664Cpu(triton::callbacks::Callbacks* callbacks=nullptr);

          //! Constructor
          TRITON_EXPORT x8664Cpu(const x8664Cpu& other);

          //! Destructor.
          TRITON_EXPORT virtual ~x8664Cpu();

          //! Copies a x8664Cpu class.
          TRITON_EXPORT x8664Cpu& operator=(const x8664Cpu& other);

          //! Returns true if regId is a GRP.
          TRITON_EXPORT bool isGPR(triton::arch::register_e regId) const;

          //! Returns true if regId is a MMX register.
          TRITON_EXPORT bool isMMX(triton::arch::register_e regId) const;

          //! Returns true if regId is a SSE register.
          TRITON_EXPORT bool isSSE(triton::arch::register_e regId) const;

          //! Returns true if regId is a AVX-256 (YMM) register.
          TRITON_EXPORT bool isAVX256(triton::arch::register_e regId) const;

          //! Returns true if regId is a AVX-512 (ZMM) register.
          TRITON_EXPORT bool isAVX512(triton::arch::register_e regId) const;

          //! Returns true if regId is a control (cr) register.
          TRITON_EXPORT bool isControl(triton::arch::register_e regId) const;

          //! Returns true if regId is a debug (dr) register.
          TRITON_EXPORT bool isDebug(triton::arch::register_e regId) const;

          //! Returns true if regId is a Segment.
          TRITON_EXPORT bool isSegment(triton::arch::register_e regId) const;

          /* Virtual pure inheritance ================================================= */
          TRITON_EXPORT bool isFlag(triton::arch::register_e regId) const;
          TRITON_EXPORT bool isRegister(triton::arch::register_e regId) const;
          TRITON_EXPORT bool isRegisterValid(triton::arch::register_e regId) const;
          TRITON_EXPORT bool isThumb(void) const;
          TRITON_EXPORT const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& getAllRegisters(void) const;
          TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;
          TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::register_e id) const;
          TRITON_EXPORT const triton::arch::Register& getProgramCounter(void) const;
          TRITON_EXPORT const triton::arch::Register& getRegister(triton::arch::register_e id) const;
          TRITON_EXPORT const triton::arch::Register& getStackPointer(void) const;
          TRITON_EXPORT std::set<const triton::arch::Register*> getParentRegisters(void) const;
          TRITON_EXPORT std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;
          TRITON_EXPORT triton::arch::endianness_e getEndianness(void) const;
          TRITON_EXPORT triton::uint32 gprBitSize(void) const;
          TRITON_EXPORT triton::uint32 gprSize(void) const;
          TRITON_EXPORT triton::uint32 numberOfRegisters(void) const;
          TRITON_EXPORT triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const;
          TRITON_EXPORT triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const;
          TRITON_EXPORT triton::uint8 getConcreteMemoryValue(triton::uint64 addr, bool execCallbacks=true) const;
          TRITON_EXPORT void clear(void);
          TRITON_EXPORT void disassembly(triton::arch::Instruction& inst) const;
          TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);
          TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);
          TRITON_EXPORT void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value);
          TRITON_EXPORT void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);
          TRITON_EXPORT void setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value);
          TRITON_EXPORT void setThumb(bool state);
          TRITON_EXPORT bool isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const;
          TRITON_EXPORT bool isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size=1) const;
          TRITON_EXPORT void clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem);
          TRITON_EXPORT void clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size=1);
          /* End of virtual pure inheritance ========================================== */
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_X8664CPU_HPP */
