//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ABSTRACTCPU_HPP
#define TRITON_ABSTRACTCPU_HPP

#include <set>

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


  /*! \interface AbstractCpu
      \brief This interface is used as abstract CPU interface. All CPU must use this interface. */
  class AbstractCpu  {
    public:
      //! Constructor.
      virtual ~AbstractCpu(){};

      //! The first function called when the a CPU is initialized.
      virtual void init(void) = 0;

      //! Clears the architecture states (registers and memory).
      virtual void clear(void) = 0;

      //! Returns true if the regId is a flag.
      /*!
          \param regId the register id.
      */
      virtual bool isFlag(triton::uint32 regId) = 0;

      //! Returns true if the regId is a register.
      /*!
          \param regId the register id.
      */
      virtual bool isReg(triton::uint32 regId) = 0;

      //! Returns true if the regId is valid.
      /*!
          \param regId the register id.
      */
      virtual bool isRegValid(triton::uint32 regId) = 0;

      //! Returns the max size (in byte) of the CPU registers (GPR).
      virtual triton::uint32 regSize(void) = 0;

      //! Returns the max size (in bit) of the CPU registers (GPR).
      virtual triton::uint32 regBitSize(void) = 0;

      //! Returns the id of the invalid CPU register.
      virtual triton::uint32 invalidReg(void) = 0;

      //! Returns the number of registers according to the CPU architecture.
      virtual triton::uint32 numberOfReg(void) = 0;

      //! Returns all information about a register id.
      /*!
          \param reg the register id.
          \return std::tuple<name, b-high, b-low, parentId>
      */
      virtual std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> getRegInfo(triton::uint32 reg) = 0;

      //! Returns all parent registers.
      virtual std::set<triton::arch::RegisterOperand*> getParentRegisters(void) = 0;

      //! Disassembles the instruction according to the architecture.
      virtual void disassembly(triton::arch::Instruction &inst) = 0;

      //! Builds the instruction semantics according to the architecture.
      virtual void buildSemantics(triton::arch::Instruction &inst) = 0;

      //! Returns the last concrete value recorded of a memory access.
      virtual triton::uint8 getLastMemoryValue(triton::__uint addr) = 0;

      //! Returns the last concrete value recorded of a memory access.
      virtual triton::uint128 getLastMemoryValue(triton::arch::MemoryOperand& mem) = 0;

      //! Returns the last concrete value recorded of a register state.
      virtual triton::uint128 getLastRegisterValue(triton::arch::RegisterOperand& reg) = 0;

      //! Sets the last concrete value of a memory access.
      virtual void setLastMemoryValue(triton::__uint addr, triton::uint8 value) = 0;

      //! Sets the last concrete value of a memory access.
      virtual void setLastMemoryValue(triton::arch::MemoryOperand& mem) = 0;

      //! Sets the last concrete value of a register state.
      virtual void setLastRegisterValue(triton::arch::RegisterOperand& reg) = 0;
  };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif  /* !ABSTRACTCPU_HPP */
