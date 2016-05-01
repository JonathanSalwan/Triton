//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ARCHITECTURE_H
#define TRITON_ARCHITECTURE_H

#include <set>
#include <vector>

#include "cpuInterface.hpp"
#include "instruction.hpp"
#include "memoryOperand.hpp"
#include "registerOperand.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Architecture namespace
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
        triton::arch::cpuInterface* cpu;

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
        triton::arch::cpuInterface* getCpu(void);

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
        std::set<triton::arch::RegisterOperand*> getAllRegisters(void) const;

        //! Returns all parent registers.
        std::set<triton::arch::RegisterOperand*> getParentRegisters(void) const;

        //! Disassembles the instruction according to the architecture.
        void disassembly(triton::arch::Instruction &inst) const;

        //! Builds the instruction semantics according to the architecture.
        void buildSemantics(triton::arch::Instruction &inst) const;

        //! Returns the last concrete value recorded of a memory access.
        triton::uint8 getLastMemoryValue(triton::__uint addr) const;

        //! Returns the last concrete value recorded of a memory access.
        triton::uint512 getLastMemoryValue(const triton::arch::MemoryOperand& mem) const;

        //! Returns the last concrete values of a memory area.
        std::vector<triton::uint8> getLastMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size) const;

        //! Returns the last concrete value recorded of a register state.
        triton::uint512 getLastRegisterValue(const triton::arch::RegisterOperand& reg) const;

        //! Sets the last concrete value of a memory access.
        void setLastMemoryValue(triton::__uint addr, triton::uint8 value);

        //! Sets the last concrete value of a memory access.
        void setLastMemoryValue(const triton::arch::MemoryOperand& mem);

        //! Sets the last concrete values of a memory area.
        void setLastMemoryAreaValue(triton::__uint baseAddr, const std::vector<triton::uint8>& values);

        //! Sets the last concrete value of a register state.
        void setLastRegisterValue(const triton::arch::RegisterOperand& reg);

        //! Constructor.
        Architecture();

        //! Destructor.
        ~Architecture();
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BITSVECTOR_H */

