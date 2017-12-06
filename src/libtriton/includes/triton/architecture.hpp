//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARCHITECTURE_H
#define TRITON_ARCHITECTURE_H

#include <set>
#include <vector>
#include <memory>

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

    /*! The architectures */
    enum architectures_e {
      ARCH_INVALID = 0, /*!< invalid architecture. */
      ARCH_X86,         /*!< x86 architecture. */
      ARCH_X86_64,      /*!< x86_64 architecture. */
      ARCH_LAST_ITEM    /*!< must be the last item.  */
    };

    /*! \class Architecture
     *  \brief The abstract architecture class. */
    class Architecture {
      private:
        //! Callbacks API
        triton::callbacks::Callbacks* callbacks;

      protected:
        //! The kind of architecture.
        triton::uint32 arch;

        //! Instance to the real CPU class.
        std::unique_ptr<triton::arch::CpuInterface> cpu;

      public:
        //! Constructor.
        TRITON_EXPORT Architecture(triton::callbacks::Callbacks* callbacks=nullptr);

        //! Returns true if the register ID is a flag.
        TRITON_EXPORT bool isFlag(triton::arch::registers_e regId) const;

        //! Returns true if the register is a flag.
        TRITON_EXPORT bool isFlag(const triton::arch::Register& reg) const;

        //! Returns true if the register ID is a register.
        TRITON_EXPORT bool isRegister(triton::arch::registers_e regId) const;

        //! Returns true if the register is a register.
        TRITON_EXPORT bool isRegister(const triton::arch::Register& reg) const;

        //! Returns true if the register ID is a register or a flag.
        TRITON_EXPORT bool isRegisterValid(triton::arch::registers_e regId) const;

        //! Returns true if the register is a register or a flag.
        TRITON_EXPORT bool isRegisterValid(const triton::arch::Register& reg) const;

        //! Returns true if the architecture is valid.
        TRITON_EXPORT bool isValid(void) const;

        //! Returns the architecture as triton::arch::architecture_e.
        TRITON_EXPORT triton::uint32 getArchitecture(void) const;

        //! Returns the CPU
        TRITON_EXPORT triton::arch::CpuInterface* getCpu(void);

        //! Returns the number of registers according to the CPU architecture.
        TRITON_EXPORT triton::uint32 numberOfRegisters(void) const;

        //! Returns the max size (in bit) of the CPU register (GPR).
        TRITON_EXPORT triton::uint32 registerBitSize(void) const;

        //! Returns the max size (in byte) of the CPU register (GPR).
        TRITON_EXPORT triton::uint32 registerSize(void) const;

        //! Setup an architecture.
        TRITON_EXPORT void setArchitecture(triton::uint32 arch);

        //! Clears the architecture states (registers and memory).
        TRITON_EXPORT void clearArchitecture(void);

        //! Returns all registers.
        TRITON_EXPORT const std::unordered_map<registers_e, const triton::arch::Register>& getAllRegisters(void) const;

        //! Returns all parent registers.
        TRITON_EXPORT std::set<const triton::arch::Register*> getParentRegisters(void) const;

        //! Returns register from id.
        TRITON_EXPORT const triton::arch::Register& getRegister(triton::arch::registers_e id) const;

        //! Returns parent register from id.
        TRITON_EXPORT const triton::arch::Register& getParentRegister(triton::arch::registers_e id) const;

        //! Returns parent register from register
        TRITON_EXPORT const triton::arch::Register& getParentRegister(const triton::arch::Register& reg) const;

        //! Disassembles the instruction according to the architecture.
        TRITON_EXPORT void disassembly(triton::arch::Instruction& inst) const;

        //! Builds the instruction semantics according to the architecture. Returns true if the instruction is supported.
        TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

        //! Returns the concrete value of a memory cell.
        TRITON_EXPORT triton::uint8 getConcreteMemoryValue(triton::uint64 addr) const;

        //! Returns the concrete value of memory cells.
        TRITON_EXPORT triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const;

        //! Returns the concrete value of a memory area.
        TRITON_EXPORT std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;

        //! Returns the concrete value of a register.
        TRITON_EXPORT triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory cell.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem, const triton::uint512& value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        TRITON_EXPORT void setConcreteRegisterValue(const triton::arch::Register& reg, const triton::uint512& value);

        //! Returns true if the range `[baseAddr:size]` is mapped into the internal memory representation. \sa getConcreteMemoryValue() and getConcreteMemoryAreaValue().
        TRITON_EXPORT bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);

        //! Removes the range `[baseAddr:size]` from the internal memory representation. \sa isMemoryMapped().
        TRITON_EXPORT void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARCHITECTURE_H */

