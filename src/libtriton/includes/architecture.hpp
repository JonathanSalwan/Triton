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

#include "cpuInterface.hpp"
#include "instruction.hpp"
#include "memoryAccess.hpp"
#include "register.hpp"
#include "tritonTypes.hpp"



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

      protected:
        //! The kind of architecture.
        triton::uint32 arch;

        //! Instance to the real CPU class.
        triton::arch::CpuInterface* cpu;

      public:

        //! Returns true if the regId is a flag.
        /*!
          \param regId the register id.
        */
        bool isFlag(triton::uint32 regId) const;

        //! Returns true if the regId is a register.
        /*!
          \param regId the register id.
        */
        bool isRegister(triton::uint32 regId) const;

        //! Returns true if the regId is a register or a flag.
        /*!
          \param regId the register id.
        */
        bool isRegisterValid(triton::uint32 regId) const;

        //! Returns true if the architecture is valid.
        bool isValid(void) const;

        //! Returns the architecture as triton::arch::architecture_e.
        triton::uint32 getArchitecture(void) const;

        //! Returns the CPU
        triton::arch::CpuInterface* getCpu(void);

        //! Returns the invalid CPU register id.
        triton::uint32 invalidRegister(void) const;

        //! Returns the number of registers according to the CPU architecture.
        triton::uint32 numberOfRegisters(void) const;

        //! Returns the max size (in bit) of the CPU register (GPR).
        triton::uint32 registerBitSize(void) const;

        //! Returns the max size (in byte) of the CPU register (GPR).
        triton::uint32 registerSize(void) const;

        //! Setup an architecture.
        /*!
          \param arch the architecture.
        */
        void setArchitecture(triton::uint32 arch);

        //! Clears the architecture states (registers and memory).
        void clearArchitecture(void);

        //! Returns all information about the register.
        /*!
          \param reg the register id.
          \return std::tuple<name, b-high, b-low, parentId>
        */
        std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> getRegisterInformation(triton::uint32 reg) const;

        //! Returns all registers.
        std::set<triton::arch::Register*> getAllRegisters(void) const;

        //! Returns all parent registers.
        std::set<triton::arch::Register*> getParentRegisters(void) const;

        //! Disassembles the instruction according to the architecture.
        void disassembly(triton::arch::Instruction& inst) const;

        //! Builds the instruction semantics according to the architecture.
        void buildSemantics(triton::arch::Instruction& inst) const;

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

        //! Constructor.
        Architecture();

        //! Destructor.
        ~Architecture();
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARCHITECTURE_H */

