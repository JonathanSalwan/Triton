//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_RISCV64CPU_HPP
#define TRITON_RISCV64CPU_HPP

#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include <triton/archEnums.hpp>
#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/riscvSpecifications.hpp>



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

    //! The riscv namespace
    namespace riscv {
    /*!
     *  \ingroup arch
     *  \addtogroup riscv
     *  @{
     */

      //! \class riscv64Cpu
      /*! \brief This class is used to describe the RV64 spec. */
      class riscv64Cpu : public CpuInterface, public riscvSpecifications {

        static const triton::arch::register_e pcId = triton::arch::ID_REG_RV64_PC;
        static const triton::arch::register_e spId = triton::arch::ID_REG_RV64_SP;

        private:
          //! Callbacks API
          triton::callbacks::Callbacks* callbacks;

          //! Capstone context
          std::size_t handle;

          //! Copies a riscv64Cpu class.
          void copy(const riscv64Cpu& other);

          //! Initializes the disassembler
          void disassInit(void);

        protected:
          /*! \brief map of address -> concrete value
           *
           * \details
           *
           * **item1**: memory address<br>
           * **item2**: concrete value
           */
          std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>> memory;

          //! Concrete value of x0
          triton::uint8 x0[triton::size::qword];
          //! Concrete value of x1
          triton::uint8 x1[triton::size::qword];
          //! Concrete value of sp
          triton::uint8 sp[triton::size::qword];
          //! Concrete value of x3
          triton::uint8 x3[triton::size::qword];
          //! Concrete value of x4
          triton::uint8 x4[triton::size::qword];
          //! Concrete value of x5
          triton::uint8 x5[triton::size::qword];
          //! Concrete value of x6
          triton::uint8 x6[triton::size::qword];
          //! Concrete value of x7
          triton::uint8 x7[triton::size::qword];
          //! Concrete value of x8
          triton::uint8 x8[triton::size::qword];
          //! Concrete value of x9
          triton::uint8 x9[triton::size::qword];
          //! Concrete value of x10
          triton::uint8 x10[triton::size::qword];
          //! Concrete value of x11
          triton::uint8 x11[triton::size::qword];
          //! Concrete value of x12
          triton::uint8 x12[triton::size::qword];
          //! Concrete value of x13
          triton::uint8 x13[triton::size::qword];
          //! Concrete value of x14
          triton::uint8 x14[triton::size::qword];
          //! Concrete value of x15
          triton::uint8 x15[triton::size::qword];
          //! Concrete value of x16
          triton::uint8 x16[triton::size::qword];
          //! Concrete value of x17
          triton::uint8 x17[triton::size::qword];
          //! Concrete value of x18
          triton::uint8 x18[triton::size::qword];
          //! Concrete value of x19
          triton::uint8 x19[triton::size::qword];
          //! Concrete value of x20
          triton::uint8 x20[triton::size::qword];
          //! Concrete value of x21
          triton::uint8 x21[triton::size::qword];
          //! Concrete value of x22
          triton::uint8 x22[triton::size::qword];
          //! Concrete value of x23
          triton::uint8 x23[triton::size::qword];
          //! Concrete value of x24
          triton::uint8 x24[triton::size::qword];
          //! Concrete value of x25
          triton::uint8 x25[triton::size::qword];
          //! Concrete value of x26
          triton::uint8 x26[triton::size::qword];
          //! Concrete value of x27
          triton::uint8 x27[triton::size::qword];
          //! Concrete value of x28
          triton::uint8 x28[triton::size::qword];
          //! Concrete value of x29
          triton::uint8 x29[triton::size::qword];
          //! Concrete value of x30
          triton::uint8 x30[triton::size::qword];
          //! Concrete value of x31
          triton::uint8 x31[triton::size::qword];
          //! Concrete value of f0
          triton::uint8 f0[triton::size::dqword];
          //! Concrete value of f1
          triton::uint8 f1[triton::size::dqword];
          //! Concrete value of f2
          triton::uint8 f2[triton::size::dqword];
          //! Concrete value of f3
          triton::uint8 f3[triton::size::dqword];
          //! Concrete value of f4
          triton::uint8 f4[triton::size::dqword];
          //! Concrete value of f5
          triton::uint8 f5[triton::size::dqword];
          //! Concrete value of f6
          triton::uint8 f6[triton::size::dqword];
          //! Concrete value of f7
          triton::uint8 f7[triton::size::dqword];
          //! Concrete value of f8
          triton::uint8 f8[triton::size::dqword];
          //! Concrete value of f9
          triton::uint8 f9[triton::size::dqword];
          //! Concrete value of f10
          triton::uint8 f10[triton::size::dqword];
          //! Concrete value of f11
          triton::uint8 f11[triton::size::dqword];
          //! Concrete value of f12
          triton::uint8 f12[triton::size::dqword];
          //! Concrete value of f13
          triton::uint8 f13[triton::size::dqword];
          //! Concrete value of f14
          triton::uint8 f14[triton::size::dqword];
          //! Concrete value of f15
          triton::uint8 f15[triton::size::dqword];
          //! Concrete value of f16
          triton::uint8 f16[triton::size::dqword];
          //! Concrete value of f17
          triton::uint8 f17[triton::size::dqword];
          //! Concrete value of f18
          triton::uint8 f18[triton::size::dqword];
          //! Concrete value of f19
          triton::uint8 f19[triton::size::dqword];
          //! Concrete value of f20
          triton::uint8 f20[triton::size::dqword];
          //! Concrete value of f21
          triton::uint8 f21[triton::size::dqword];
          //! Concrete value of f22
          triton::uint8 f22[triton::size::dqword];
          //! Concrete value of f23
          triton::uint8 f23[triton::size::dqword];
          //! Concrete value of f24
          triton::uint8 f24[triton::size::dqword];
          //! Concrete value of f25
          triton::uint8 f25[triton::size::dqword];
          //! Concrete value of f26
          triton::uint8 f26[triton::size::dqword];
          //! Concrete value of f27
          triton::uint8 f27[triton::size::dqword];
          //! Concrete value of f28
          triton::uint8 f28[triton::size::dqword];
          //! Concrete value of f29
          triton::uint8 f29[triton::size::dqword];
          //! Concrete value of f30
          triton::uint8 f30[triton::size::dqword];
          //! Concrete value of f31
          triton::uint8 f31[triton::size::dqword];
          //! Concrete value of pc
          triton::uint8 pc[triton::size::qword];

          //! System registers
          #define SYS_REG_SPEC(_, LOWER_NAME, _2, _3, _4, _5, _6) \
          triton::uint8 LOWER_NAME[triton::size::qword];
          #define REG_SPEC(_1, _2, _3, _4, _5, _6, _7)
          #define REG_SPEC_NO_CAPSTONE(_1, _2, _3, _4, _5, _6, _7)
          #include "triton/riscv64.spec"

        public:
          //! Constructor.
          TRITON_EXPORT riscv64Cpu(triton::callbacks::Callbacks* callbacks=nullptr);

          //! Constructor
          TRITON_EXPORT riscv64Cpu(const riscv64Cpu& other);

          //! Destructor.
          TRITON_EXPORT virtual ~riscv64Cpu();

          //! Copies a riscv64Cpu class.
          TRITON_EXPORT riscv64Cpu& operator=(const riscv64Cpu& other);

          //! Returns true if regId is a GRP.
          TRITON_EXPORT bool isGPR(triton::arch::register_e regId) const;

          //! Returns true if regId is a FPU register.
          TRITON_EXPORT bool isFPU(triton::arch::register_e regId) const;

          /* Virtual pure inheritance ================================================= */
          TRITON_EXPORT bool isFlag(triton::arch::register_e regId) const;
          TRITON_EXPORT bool isRegister(triton::arch::register_e regId) const;
          TRITON_EXPORT bool isRegisterValid(triton::arch::register_e regId) const;
          TRITON_EXPORT bool isThumb(void) const;
          TRITON_EXPORT bool isMemoryExclusive(const triton::arch::MemoryAccess& mem) const;
          TRITON_EXPORT const std::unordered_map<triton::arch::register_e, const triton::arch::Register>& getAllRegisters(void) const;
          TRITON_EXPORT const std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>>& getConcreteMemory(void) const;
          TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;
          TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::register_e id) const;
          TRITON_EXPORT const triton::arch::Register& getProgramCounter(void) const;
          TRITON_EXPORT const triton::arch::Register& getRegister(triton::arch::register_e id) const;
          TRITON_EXPORT const triton::arch::Register& getRegister(const std::string& name) const;
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
          TRITON_EXPORT void disassembly(triton::arch::Instruction& inst);
          TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values, bool execCallbacks=true);
          TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const void* area, triton::usize size, bool execCallbacks=true);
          TRITON_EXPORT void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value, bool execCallbacks=true);
          TRITON_EXPORT void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value, bool execCallbacks=true);
          TRITON_EXPORT void setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value, bool execCallbacks=true);
          TRITON_EXPORT void setThumb(bool state);
          TRITON_EXPORT void setMemoryExclusiveTag(const triton::arch::MemoryAccess& mem, bool tag);
          TRITON_EXPORT bool isConcreteMemoryValueDefined(const triton::arch::MemoryAccess& mem) const;
          TRITON_EXPORT bool isConcreteMemoryValueDefined(triton::uint64 baseAddr, triton::usize size=1) const;
          TRITON_EXPORT void clearConcreteMemoryValue(const triton::arch::MemoryAccess& mem);
          TRITON_EXPORT void clearConcreteMemoryValue(triton::uint64 baseAddr, triton::usize size=1);
          /* End of virtual pure inheritance ========================================== */
      };

    /*! @} End of riscv namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_RISCV64CPU_HPP */
