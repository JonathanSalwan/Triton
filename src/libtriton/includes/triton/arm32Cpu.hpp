//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_ARM32CPU_HPP
#define TRITON_ARM32CPU_HPP

#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include <triton/archEnums.hpp>
#include <triton/arm32Specifications.hpp>
#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/dllexport.hpp>
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

      //! The arm32 namespace
      namespace arm32 {
      /*!
       *  \ingroup arm
       *  \addtogroup arm32
       *  @{
       */

        //! \class Arm32Cpu
        /*! \brief This class is used to describe the ARM (32-bits) spec. */
        class Arm32Cpu : public CpuInterface, public Arm32Specifications {

          static const triton::arch::register_e pcId = triton::arch::ID_REG_ARM32_PC;
          static const triton::arch::register_e spId = triton::arch::ID_REG_ARM32_SP;

          private:
            //! Callbacks API
            triton::callbacks::Callbacks* callbacks;

            //! Capstone context for ARM mode.
            std::size_t handleArm;

            //! Capstone context for Thumb mode.
            std::size_t handleThumb;

            //! State of the currently processed IT block.
            char itStateArray[5];

            //! Number of instructions not yet processed in the IT block.
            triton::uint32 itInstrsCount;

            //! Index of the instruction currently processed in the IT block.
            triton::uint32 itInstrIndex;

            //! Condition code of the currently processed IT block.
            triton::arch::arm::condition_e itCC;

            //! Inverted condition code of the currently processed IT block.
            triton::arch::arm::condition_e itCCInv;

            //! Exclusive memory tags. Each address in this std::set is tagged as exclusive.
            std::set<triton::uint64> exclusiveMemoryTags;

            //! Copies a Arm32Cpu class.
            void copy(const Arm32Cpu& other);

            //! Initializes the disassembler.
            inline void disassInit(void);

            //! Post process instructions to provide a uniformity among ARM and Thumb modes.
            void postDisassembly(triton::arch::Instruction& inst) const;

            //! Given a condition code it returns its opposite code (mainly used when processing IT instructions).
            triton::arch::arm::condition_e invertCodeCondition(triton::arch::arm::condition_e cc) const;

          protected:
            /*! \brief map of address -> concrete value
             *
             * \details
             *
             * **item1**: memory address<br>
             * **item2**: concrete value
             */
            std::unordered_map<triton::uint64, triton::uint8, IdentityHash<triton::uint64>> memory;

            //! Concrete value of r0
            triton::uint8 r0[triton::size::dword];
            //! Concrete value of r1
            triton::uint8 r1[triton::size::dword];
            //! Concrete value of r2
            triton::uint8 r2[triton::size::dword];
            //! Concrete value of r3
            triton::uint8 r3[triton::size::dword];
            //! Concrete value of r4
            triton::uint8 r4[triton::size::dword];
            //! Concrete value of r5
            triton::uint8 r5[triton::size::dword];
            //! Concrete value of r6
            triton::uint8 r6[triton::size::dword];
            //! Concrete value of r7
            triton::uint8 r7[triton::size::dword];
            //! Concrete value of r8
            triton::uint8 r8[triton::size::dword];
            //! Concrete value of r9
            triton::uint8 r9[triton::size::dword];
            //! Concrete value of r10
            triton::uint8 r10[triton::size::dword];
            //! Concrete value of r11
            triton::uint8 r11[triton::size::dword];
            //! Concrete value of r12
            triton::uint8 r12[triton::size::dword];
            //! Concrete value of sp
            triton::uint8 sp[triton::size::dword];
            //! Concrete value of r14
            triton::uint8 r14[triton::size::dword];
            //! Concrete value of pc
            triton::uint8 pc[triton::size::dword];
            // //! Concrete value of apsr
            triton::uint8 apsr[triton::size::dword];

            //! Thumb mode flag
            bool thumb;

          public:
            //! Constructor.
            TRITON_EXPORT Arm32Cpu(triton::callbacks::Callbacks* callbacks=nullptr);

            //! Constructor
            TRITON_EXPORT Arm32Cpu(const Arm32Cpu& other);

            //! Destructor.
            TRITON_EXPORT virtual ~Arm32Cpu();

            //! Copies a Arm32Cpu class.
            TRITON_EXPORT Arm32Cpu& operator=(const Arm32Cpu& other);

            //! Returns true if regId is a GRP.
            TRITON_EXPORT bool isGPR(triton::arch::register_e regId) const;

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
            TRITON_EXPORT triton::uint32 gprBitSize(void) const;
            TRITON_EXPORT triton::uint32 gprSize(void) const;
            TRITON_EXPORT triton::uint32 numberOfRegisters(void) const;
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

      /*! @} End of arm32 namespace */
      };
    /*! @} End of arm namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARM32CPU_HPP */
