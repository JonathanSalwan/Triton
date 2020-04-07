//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_X86CPU_HPP
#define TRITON_X86CPU_HPP

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

      //! \class x86Cpu
      /*! \brief This class is used to describe the x86 (32-bits) spec. */
      class x86Cpu : public CpuInterface, public x86Specifications {

        static const triton::arch::register_e pcId = triton::arch::ID_REG_X86_EIP;
        static const triton::arch::register_e spId = triton::arch::ID_REG_X86_ESP;

        private:
          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

          //! Capstone context
          triton::extlibs::capstone::csh handle;

          //! Copies a x86Cpu class.
          void copy(const x86Cpu& other);

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

          //! Concrete value of eax
          triton::uint8 eax[triton::size::dword];
          //! Concrete value of ebx
          triton::uint8 ebx[triton::size::dword];
          //! Concrete value of ecx
          triton::uint8 ecx[triton::size::dword];
          //! Concrete value of edx
          triton::uint8 edx[triton::size::dword];
          //! Concrete value of edi
          triton::uint8 edi[triton::size::dword];
          //! Concrete value of esi
          triton::uint8 esi[triton::size::dword];
          //! Concrete value of ebp
          triton::uint8 ebp[triton::size::dword];
          //! Concrete value of esp
          triton::uint8 esp[triton::size::dword];
          //! Concrete value of eip
          triton::uint8 eip[triton::size::dword];
          //! Concrete value of eflags
          triton::uint8 eflags[triton::size::dword];
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
          //! Concrete value of ymm0
          triton::uint8 ymm0[triton::size::qqword];
          //! Concrete value of ymm1
          triton::uint8 ymm1[triton::size::qqword];
          //! Concrete value of ymm2
          triton::uint8 ymm2[triton::size::qqword];
          //! Concrete value of ymm3
          triton::uint8 ymm3[triton::size::qqword];
          //! Concrete value of ymm4
          triton::uint8 ymm4[triton::size::qqword];
          //! Concrete value of ymm5
          triton::uint8 ymm5[triton::size::qqword];
          //! Concrete value of ymm6
          triton::uint8 ymm6[triton::size::qqword];
          //! Concrete value of ymm7
          triton::uint8 ymm7[triton::size::qqword];
          //! Concrete value of mxcsr
          triton::uint8 mxcsr[triton::size::dword];
          //! Concrete value of cr0
          triton::uint8 cr0[triton::size::dword];
          //! Concrete value of cr1
          triton::uint8 cr1[triton::size::dword];
          //! Concrete value of cr2
          triton::uint8 cr2[triton::size::dword];
          //! Concrete value of cr3
          triton::uint8 cr3[triton::size::dword];
          //! Concrete value of cr4
          triton::uint8 cr4[triton::size::dword];
          //! Concrete value of cr5
          triton::uint8 cr5[triton::size::dword];
          //! Concrete value of cr6
          triton::uint8 cr6[triton::size::dword];
          //! Concrete value of cr7
          triton::uint8 cr7[triton::size::dword];
          //! Concrete value of cr8
          triton::uint8 cr8[triton::size::dword];
          //! Concrete value of cr9
          triton::uint8 cr9[triton::size::dword];
          //! Concrete value of cr10
          triton::uint8 cr10[triton::size::dword];
          //! Concrete value of cr11
          triton::uint8 cr11[triton::size::dword];
          //! Concrete value of cr12
          triton::uint8 cr12[triton::size::dword];
          //! Concrete value of cr13
          triton::uint8 cr13[triton::size::dword];
          //! Concrete value of cr14
          triton::uint8 cr14[triton::size::dword];
          //! Concrete value of cr15
          triton::uint8 cr15[triton::size::dword];
          //! Concrete value of CS
          triton::uint8 cs[triton::size::dword];
          //! Concrete value of DS
          triton::uint8 ds[triton::size::dword];
          //! Concrete value of ES
          triton::uint8 es[triton::size::dword];
          //! Concrete value of FS
          triton::uint8 fs[triton::size::dword];
          //! Concrete value of GS
          triton::uint8 gs[triton::size::dword];
          //! Concrete value of SS
          triton::uint8 ss[triton::size::dword];
          //! Concrete value of dr0
          triton::uint8 dr0[triton::size::dword];
          //! Condete value of dr1
          triton::uint8 dr1[triton::size::dword];
          //! Condete value of dr2
          triton::uint8 dr2[triton::size::dword];
          //! Condete value of dr3
          triton::uint8 dr3[triton::size::dword];
          //! Condete value of dr6
          triton::uint8 dr6[triton::size::dword];
          //! Condete value of dr7
          triton::uint8 dr7[triton::size::dword];

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
          TRITON_EXPORT bool isGPR(triton::arch::register_e regId) const;

          //! Returns true if regId is a MMX register.
          TRITON_EXPORT bool isMMX(triton::arch::register_e regId) const;

          //! Returns true if regId is a SSE register.
          TRITON_EXPORT bool isSSE(triton::arch::register_e regId) const;

          //! Returns true if regId is a AVX-256 (YMM) register.
          TRITON_EXPORT bool isAVX256(triton::arch::register_e regId) const;

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
          TRITON_EXPORT triton::uint32 numberOfRegisters(void) const;
          TRITON_EXPORT triton::uint32 gprBitSize(void) const;
          TRITON_EXPORT triton::uint32 gprSize(void) const;
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

#endif /* TRITON_X86CPU_HPP */
