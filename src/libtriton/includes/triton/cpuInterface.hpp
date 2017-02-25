//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_CPUINTERFACE_HPP
#define TRITON_CPUINTERFACE_HPP

#include <set>
#include <vector>

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

    /*! \interface CpuInterface
        \brief This interface is used as abstract CPU interface. All CPU must use this interface. */
    class CpuInterface {
      public:
        //! Destructor.
        virtual ~CpuInterface(){};

        //! The first function called when the a CPU is initialized.
        virtual void init(void) = 0;

        //! Clears the architecture states (registers and memory).
        virtual void clear(void) = 0;

        //! Returns true if the register ID is a flag.
        virtual bool isFlag(triton::uint32 regId) const = 0;

        //! Returns true if the register ID is a register.
        virtual bool isRegister(triton::uint32 regId) const = 0;

        //! Returns true if the register ID is valid.
        virtual bool isRegisterValid(triton::uint32 regId) const = 0;

        //! Returns the max size (in byte) of the CPU registers (GPR).
        virtual triton::uint32 registerSize(void) const = 0;

        //! Returns the max size (in bit) of the CPU registers (GPR).
        virtual triton::uint32 registerBitSize(void) const = 0;

        //! Returns the number of registers according to the CPU architecture.
        virtual triton::uint32 numberOfRegisters(void) const = 0;

        //! Returns all information about a register id.
        virtual triton::arch::RegisterSpecification getRegisterSpecification(triton::uint32 regId) const = 0;

        //! Returns all registers.
        virtual std::set<triton::arch::Register*> getAllRegisters(void) const = 0;

        //! Returns all parent registers.
        virtual std::set<triton::arch::Register*> getParentRegisters(void) const = 0;

        //! Disassembles the instruction according to the architecture.
        virtual void disassembly(triton::arch::Instruction& inst) const = 0;

        //! Returns the concrete value of a memory cell.
        virtual triton::uint8 getConcreteMemoryValue(triton::uint64 addr) const = 0;

        //! Returns the concrete value of memory cells.
        virtual triton::uint512 getConcreteMemoryValue(const triton::arch::MemoryAccess& mem, bool execCallbacks=true) const = 0;

        //! Returns the concrete value of a memory area.
        virtual std::vector<triton::uint8> getConcreteMemoryAreaValue(triton::uint64 baseAddr, triton::usize size, bool execCallbacks=true) const = 0;

        //! Returns the concrete value of a register.
        virtual triton::uint512 getConcreteRegisterValue(const triton::arch::Register& reg, bool execCallbacks=true) const = 0;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory cell.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        virtual void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value) = 0;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        virtual void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem) = 0;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        virtual void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values) = 0;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        virtual void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size) = 0;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \description Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        virtual void setConcreteRegisterValue(const triton::arch::Register& reg) = 0;

        //! Returns true if the range `[baseAddr:size]` is mapped into the internal memory representation. \sa getConcreteMemoryValue() and getConcreteMemoryAreaValue().
        virtual bool isMemoryMapped(triton::uint64 baseAddr, triton::usize size=1) = 0;

        //! Removes the range `[baseAddr:size]` from the internal memory representation. \sa isMemoryMapped().
        virtual void unmapMemory(triton::uint64 baseAddr, triton::usize size=1) = 0;
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_CPUINTERFACE_HPP */
