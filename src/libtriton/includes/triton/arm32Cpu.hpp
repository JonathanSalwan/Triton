//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARM32CPU_HPP
#define TRITON_ARM32CPU_HPP

#include <map>
#include <set>
#include <vector>

#include <triton/archEnums.hpp>
#include <triton/callbacks.hpp>
#include <triton/cpuInterface.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/tritonTypes.hpp>
#include <triton/arm32Specifications.hpp>



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

            //! Copies a Arm32Cpu class.
            void copy(const Arm32Cpu& other);

          protected:
            /*! \brief map of address -> concrete value
             *
             * \details
             * **item1**: memory address<br>
             * **item2**: concrete value
             */
            std::map<triton::uint64, triton::uint8> memory;

            //! Concrete value of r0
            triton::uint8 r0[DWORD_SIZE];
            //! Concrete value of r1
            triton::uint8 r1[DWORD_SIZE];
            //! Concrete value of r2
            triton::uint8 r2[DWORD_SIZE];
            //! Concrete value of r3
            triton::uint8 r3[DWORD_SIZE];
            //! Concrete value of r4
            triton::uint8 r4[DWORD_SIZE];
            //! Concrete value of r5
            triton::uint8 r5[DWORD_SIZE];
            //! Concrete value of r6
            triton::uint8 r6[DWORD_SIZE];
            //! Concrete value of r7
            triton::uint8 r7[DWORD_SIZE];
            //! Concrete value of r8
            triton::uint8 r8[DWORD_SIZE];
            //! Concrete value of r9
            triton::uint8 r9[DWORD_SIZE];
            //! Concrete value of r10
            triton::uint8 r10[DWORD_SIZE];
            //! Concrete value of r11
            triton::uint8 r11[DWORD_SIZE];
            //! Concrete value of r12
            triton::uint8 r12[DWORD_SIZE];
            //! Concrete value of sp
            triton::uint8 sp[DWORD_SIZE];
            //! Concrete value of r14
            triton::uint8 r14[DWORD_SIZE];
            //! Concrete value of pc
            triton::uint8 pc[DWORD_SIZE];
            // //! Concrete value of apsr
            triton::uint8 apsr[DWORD_SIZE];

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

            //! Returns true if CPU is in Thumb mode.
            TRITON_EXPORT bool isThumb(void) const;

            //! Sets CPU state to Thumb mode.
            TRITON_EXPORT void setThumb(bool state);

            /* Virtual pure inheritance ================================================= */
            TRITON_EXPORT bool isFlag(triton::arch::register_e regId) const;
            TRITON_EXPORT bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);
            TRITON_EXPORT bool isRegister(triton::arch::register_e regId) const;
            TRITON_EXPORT bool isRegisterValid(triton::arch::register_e regId) const;
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
            TRITON_EXPORT void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);
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
