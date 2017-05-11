//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARCHITECTURE_H
#define TRITON_ARCHITECTURE_H

#include <triton/tritonTypes.hpp>  // for uint32, uint64, uint8, usize, uint512
#include "triton/registers_e.hpp"  // for registers_e
#include "triton/cpuInterface.hpp" // for unique_ptr<CpuInterface>
#include <unordered_map>           // for std::unordered_map
#include <set>                     // for std::set
#include <vector>                  // for std::vector


//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  namespace callbacks {
    class Callbacks;
  }

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    class CpuInterface;
    class Instruction;
    class MemoryAccess;
    class RegisterSpec;
    class Register;

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
        bool isFlag(triton::arch::registers_e regId) const;

        //! Returns true if the register is a flag.
        bool isFlag(const triton::arch::RegisterSpec& reg) const;

        //! Returns true if the register ID is a register.
        bool isRegister(triton::arch::registers_e regId) const;

        //! Returns true if the register is a register.
        bool isRegister(const triton::arch::RegisterSpec& reg) const;

        //! Returns true if the register ID is a register or a flag.
        bool isRegisterValid(triton::arch::registers_e regId) const;

        //! Returns true if the register is a register or a flag.
        bool isRegisterValid(const triton::arch::RegisterSpec& reg) const;

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

        //! Returns all registers.
        const std::unordered_map<registers_e, const triton::arch::RegisterSpec>& getAllRegisters(void) const;

        //! Returns all parent registers.
        std::set<const triton::arch::RegisterSpec*> getParentRegisters(void) const;

        //! Get register from id.
        const triton::arch::RegisterSpec& getRegister(triton::arch::registers_e id) const;

        //! Get parent register from id.
        const triton::arch::RegisterSpec& getParentRegister(triton::arch::registers_e id) const;

        //! Get parent register from register
        const triton::arch::RegisterSpec& getParentRegister(const triton::arch::RegisterSpec& reg) const;

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
        triton::uint512 getConcreteRegisterValue(const triton::arch::RegisterSpec& reg, bool execCallbacks=true) const;

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory cell.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryValue(triton::uint64 addr, triton::uint8 value);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of memory cells.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryValue(const triton::arch::MemoryAccess& mem);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const std::vector<triton::uint8>& values);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a memory area.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
         * with the symbolic state (if it exists). You should probably use the concretize functions after this.
         */
        void setConcreteMemoryAreaValue(triton::uint64 baseAddr, const triton::uint8* area, triton::usize size);

        /*!
         * \brief [**architecture api**] - Sets the concrete value of a register.
         *
         * \details Note that by setting a concrete value will probably imply a desynchronization
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

