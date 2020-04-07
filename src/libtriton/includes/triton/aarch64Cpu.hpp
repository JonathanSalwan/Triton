//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_AARCH64CPU_HPP
#define TRITON_AARCH64CPU_HPP

#include <set>
#include <unordered_map>
#include <vector>

#include <triton/aarch64Specifications.hpp>
#include <triton/archEnums.hpp>
#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/dllexport.hpp>
#include <triton/externalLibs.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/tritonTypes.hpp>



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

    //! The ARM namespace
    namespace arm {
    /*!
     *  \ingroup arch
     *  \addtogroup arm
     *  @{
     */

      //! The aarch64 namespace
      namespace aarch64 {
      /*!
       *  \ingroup arm
       *  \addtogroup aarch64
       *  @{
       */

        //! \class AArch64Cpu
        /*! \brief This class is used to describe the ARM (64-bits) spec. */
        class AArch64Cpu : public CpuInterface, public AArch64Specifications {

          static const triton::arch::register_e pcId = triton::arch::ID_REG_AARCH64_PC;
          static const triton::arch::register_e spId = triton::arch::ID_REG_AARCH64_SP;

          private:
            //! Callbacks API
            triton::callbacks::Callbacks* callbacks;

            //! Capstone context
            triton::extlibs::capstone::csh handle;

            //! Copies a AArch64Cpu class.
            void copy(const AArch64Cpu& other);

            //! Initializes the disassembler
            inline void disassInit(void);

          protected:
            /*! \brief map of address -> concrete value
             *
             * \details
             * **item1**: memory address<br>
             * **item2**: concrete value
             */
            std::unordered_map<triton::uint64, triton::uint8> memory;

            //! Concrete value of x0
            triton::uint8 x0[triton::size::qword];
            //! Concrete value of x1
            triton::uint8 x1[triton::size::qword];
            //! Concrete value of x2
            triton::uint8 x2[triton::size::qword];
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
            //! Concrete value of sp
            triton::uint8 sp[triton::size::qword];
            //! Concrete value of pc
            triton::uint8 pc[triton::size::qword];
            //! Concrete value of spsr
            triton::uint8 spsr[triton::size::dword];

          public:
            //! Constructor.
            TRITON_EXPORT AArch64Cpu(triton::callbacks::Callbacks* callbacks=nullptr);

            //! Constructor
            TRITON_EXPORT AArch64Cpu(const AArch64Cpu& other);

            //! Destructor.
            TRITON_EXPORT virtual ~AArch64Cpu();

            //! Copies a AArch64Cpu class.
            TRITON_EXPORT AArch64Cpu& operator=(const AArch64Cpu& other);

            //! Returns true if regId is a GRP.
            TRITON_EXPORT bool isGPR(triton::arch::register_e regId) const;

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

      /*! @} End of aarch64 namespace */
      };
    /*! @} End of arm namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_AARCH64CPU_HPP */
