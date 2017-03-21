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
#include <triton/instruction.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/registerSpecification.hpp>
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
        Architecture(triton::callbacks::Callbacks* callbacks=nullptr);

        //! Returns true if the register ID is a flag.
        bool isFlag(triton::uint32 regId) const;

        //! Returns true if the register is a flag.
        bool isFlag(const triton::arch::Register& reg) const;

        //! Returns true if the register ID is a register.
        bool isRegister(triton::uint32 regId) const;

        //! Returns true if the register is a register.
        bool isRegister(const triton::arch::Register& reg) const;

        //! Returns true if the register ID is a register or a flag.
        bool isRegisterValid(triton::uint32 regId) const;

        //! Returns true if the register is a register or a flag.
        bool isRegisterValid(const triton::arch::Register& reg) const;

        //! Returns true if the architecture is valid.
        bool isValid(void) const;

        //! Returns the architecture as triton::arch::architecture_e.
        triton::uint32 getArchitecture(void) const;

        //! Returns the CPU
        triton::arch::CpuInterface* getCpu(void);

        //! Returns the number of registers according to the CPU architecture.
        triton::uint32 numberOfRegisters(void) const;

        //! Returns the max size (in bit) of the CPU register (GPR).
        triton::uint32 registerBitSize(void) const;

        //! Returns the max size (in byte) of the CPU register (GPR).
        triton::uint32 registerSize(void) const;

        //! Setup an architecture.
        void setArchitecture(triton::uint32 arch);

        //! Clears the architecture states (registers and memory).
        void clearArchitecture(void);

        //! Returns all information about the register.
        triton::arch::RegisterSpecification getRegisterSpecification(triton::uint32 regId) const;

        //! Returns all registers.
        std::set<triton::arch::Register*> getAllRegisters(void) const;

        //! Returns all parent registers.
        std::set<triton::arch::Register*> getParentRegisters(void) const;

        //! Disassembles the instruction according to the architecture.
        void disassembly(triton::arch::Instruction& inst) const;

        //! Builds the instruction semantics according to the architecture. Returns true if the instruction is supported.
        bool buildSemantics(triton::arch::Instruction& inst);

        //! Returns the concrete value of a memory cell.
        triton::uint8 getConcreteMemoryValue(triton::uint64 addr) const;

        //! Returns the concrete value of memory cells.
        triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const;

        //! Returns the concrete value of a memory area.
        std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const;

        //! Returns the concrete value of a register.
        triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory cell.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteRegisterValue(const triton::arch::Register& reg);

        //! Returns true if the range `[baseAddr:size]` is mapped into the internal memory representation. \sa getConcreteMemoryValue() and getConcreteMemoryAreaValue().
        bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1);

        //! Removes the range `[baseAddr:size]` from the internal memory representation. \sa isMemoryMapped().
        void unmapMemory(triton::uint64 baseAddr, triton::usize size=1);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARCHITECTURE_H */

