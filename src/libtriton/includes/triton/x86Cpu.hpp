//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_X86CPU_HPP
#define TRITON_X86CPU_HPP

#include <map>
#include <set>
#include <vector>

#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/registers_e.hpp>
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

      //! \class x86Cpu
      /*! \brief This class is used to describe the x86 (32-bits) spec. */
      class x86Cpu : public CpuInterface, public x86Specifications {

        static constexpr registers_e pcId = ID_REG_EIP;

        private:
          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

          //! Copies a x86Cpu class.
          void copy(const x86Cpu& other);

        protected:
          /*! \brief map of address -> concrete value
           *
           * \details
           * **item1**: memory address<br>
           * **item2**: concrete value
           */
          std::map<triton::uint64, triton::uint8> memory;

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
          //! Concrete value of mxcsr
          triton::uint8 mxcsr[DWORD_SIZE];
          //! Concrete value of cr0
          triton::uint8 cr0[DWORD_SIZE];
          //! Concrete value of cr1
          triton::uint8 cr1[DWORD_SIZE];
          //! Concrete value of cr2
          triton::uint8 cr2[DWORD_SIZE];
          //! Concrete value of cr3
          triton::uint8 cr3[DWORD_SIZE];
          //! Concrete value of cr4
          triton::uint8 cr4[DWORD_SIZE];
          //! Concrete value of cr5
          triton::uint8 cr5[DWORD_SIZE];
          //! Concrete value of cr6
          triton::uint8 cr6[DWORD_SIZE];
          //! Concrete value of cr7
          triton::uint8 cr7[DWORD_SIZE];
          //! Concrete value of cr8
          triton::uint8 cr8[DWORD_SIZE];
          //! Concrete value of cr9
          triton::uint8 cr9[DWORD_SIZE];
          //! Concrete value of cr10
          triton::uint8 cr10[DWORD_SIZE];
          //! Concrete value of cr11
          triton::uint8 cr11[DWORD_SIZE];
          //! Concrete value of cr12
          triton::uint8 cr12[DWORD_SIZE];
          //! Concrete value of cr13
          triton::uint8 cr13[DWORD_SIZE];
          //! Concrete value of cr14
          triton::uint8 cr14[DWORD_SIZE];
          //! Concrete value of cr15
          triton::uint8 cr15[DWORD_SIZE];
          //! Concrete value of CS
          triton::uint8 cs[DWORD_SIZE];
          //! Concrete value of DS
          triton::uint8 ds[DWORD_SIZE];
          //! Concrete value of ES
          triton::uint8 es[DWORD_SIZE];
          //! Concrete value of FS
          triton::uint8 fs[DWORD_SIZE];
          //! Concrete value of GS
          triton::uint8 gs[DWORD_SIZE];
          //! Concrete value of SS
          triton::uint8 ss[DWORD_SIZE];

        public:
          //! Constructor.
          TRITON_EXPORT x86Cpu(triton::callbacks::Callbacks* callbacks=nullptr);

          //! Copy constructor
          TRITON_EXPORT x86Cpu(const x86Cpu& other);

          //! Destructor.
          TRITON_EXPORT virtual ~x86Cpu();

          //! Copies a x86Cpu class.
          TRITON_EXPORT x86Cpu& operator=(const x86Cpu& other);

          //! Returns true if regId is a GRP.
          TRITON_EXPORT bool isGPR(triton::arch::registers_e regId) const;

          //! Returns true if regId is a MMX register.
          TRITON_EXPORT bool isMMX(triton::arch::registers_e regId) const;

          //! Returns true if regId is a SSE register.
          TRITON_EXPORT bool isSSE(triton::arch::registers_e regId) const;

          //! Returns true if regId is a AVX-256 (YMM) register.
          TRITON_EXPORT bool isAVX256(triton::arch::registers_e regId) const;

          //! Returns true if regId is a control (cr) register.
          TRITON_EXPORT bool isControl(triton::arch::registers_e regId) const;

          //! Returns true if regId is a Segment.
          TRITON_EXPORT bool isSegment(triton::arch::registers_e regId) const;

          /* Virtual pure inheritance ================================================= */
          TRITON_EXPORT bool isFlag(triton::arch::registers_e regId) const;
          TRITON_EXPORT bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);
          TRITON_EXPORT bool isRegister(triton::arch::registers_e regId) const;
          TRITON_EXPORT bool isRegisterValid(triton::arch::registers_e regId) const;
          TRITON_EXPORT const std::unordered_map<registers_e, const triton::arch::Register>& getAllRegisters(void) const;
          TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;
          TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::registers_e id) const;
          TRITON_EXPORT const triton::arch::Register& getRegister(triton::arch::registers_e id) const;
          TRITON_EXPORT std::set<const triton::arch::Register*> getParentRegisters(void) const;
          TRITON_EXPORT std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;
          TRITON_EXPORT triton::uint32 numberOfRegisters(void) const;
          TRITON_EXPORT triton::uint32 registerBitSize(void) const;
          TRITON_EXPORT triton::uint32 registerSize(void) const;
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
          TRITON_EXPORT void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);
          /* End of virtual pure inheritance ========================================== */
      };

    /*! @} End of x86 namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};


#endif  /* !X86CPU_HPP */
