//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TAINTENGINE_H
#define TRITON_TAINTENGINE_H

#include <set>

#include <triton/triton_export.h>
#include <triton/memoryAccess.hpp>
#include <triton/modes.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Taint namespace
    namespace taint {
    /*!
     *  \ingroup engines
     *  \addtogroup taint
     *  @{
     */

      //! Defines a tainted item.
      const bool TAINTED = true;

      //! Defines an untainted item.
      const bool UNTAINTED = !TAINTED;

      /*! \class TaintEngine
          \brief The taint engine class. */
      class TaintEngine {
        private:
          //! Modes API
          triton::modes::SharedModes modes;

          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

          //! Cpu API
          triton::arch::CpuInterface& cpu;

        protected:
          //! Defines if the taint engine is enabled or disabled.
          bool enableFlag;

          //! The set of tainted addresses.
          std::set<triton::uint64> taintedMemory;

          //! The set of tainted registers. Currently it is an over approximation of the taint.
          std::set<triton::arch::register_e> taintedRegisters;

        public:
          //! Constructor.
          TRITON_EXPORT TaintEngine(const triton::modes::SharedModes& modes, triton::engines::symbolic::SymbolicEngine* symbolicEngine, triton::arch::CpuInterface& cpu);

          //! Constructor by copy.
          TRITON_EXPORT TaintEngine(const TaintEngine& other);

          //! Copies a TaintEngine.
          TRITON_EXPORT TaintEngine& operator=(const TaintEngine& other);

          //! Enables or disables the taint engine.
          TRITON_EXPORT void enable(bool flag);

          //! Returns the tainted addresses.
          TRITON_EXPORT const std::set<triton::uint64>& getTaintedMemory(void) const;

          //! Returns the tainted registers.
          TRITON_EXPORT std::set<const triton::arch::Register*> getTaintedRegisters(void) const;

          //! Returns true if the taint engine is enabled.
          TRITON_EXPORT bool isEnabled(void) const;

          //! Returns true if the addr is tainted.
          TRITON_EXPORT bool isMemoryTainted(triton::uint64 addr, triton::uint32 size=1) const;

          //! Returns true if the memory is tainted.
          TRITON_EXPORT bool isMemoryTainted(const triton::arch::MemoryAccess& mem, bool mode=true) const;

          //! Returns true if the register is tainted.
          TRITON_EXPORT bool isRegisterTainted(const triton::arch::Register& reg) const;

          //! Abstract taint verification. Returns true if the operand is tainted.
          TRITON_EXPORT bool isTainted(const triton::arch::OperandWrapper& op) const;

          //! Sets the flag (taint or untaint) to an abstract operand (Register or Memory).
          TRITON_EXPORT bool setTaint(const triton::arch::OperandWrapper& op, bool flag);

          //! Sets the flag (taint or untaint) to a memory.
          TRITON_EXPORT bool setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag);

          //! Sets the flag (taint or untaint) to a register.
          TRITON_EXPORT bool setTaintRegister(const triton::arch::Register& reg, bool flag);

          //! Taints an address. Returns TAINTED if the address has been tainted correctly. Otherwise it returns the last defined state.
          TRITON_EXPORT bool taintMemory(triton::uint64 addr);

          //! Taints a memory. Returns TAINTED if the memory has been tainted correctly. Otherwise it returns the last defined state.
          TRITON_EXPORT bool taintMemory(const triton::arch::MemoryAccess& mem);

          //! Taints a register. Returns TAINTED if the register has been tainted correctly. Otherwise it returns the last defined state.
          TRITON_EXPORT bool taintRegister(const triton::arch::Register& reg);

          //! Untaints an address. Returns !TAINTED if the address has been untainted correctly. Otherwise it returns the last defined state.
          TRITON_EXPORT bool untaintMemory(triton::uint64 addr);

          //! Untaints a memory. Returns !TAINTED if the memory has been untainted correctly. Otherwise it returns the last defined state.
          TRITON_EXPORT bool untaintMemory(const triton::arch::MemoryAccess& mem);

          //! Untaints a register. Returns !TAINTED if the register has been untainted correctly. Otherwise it returns the last defined state.
          TRITON_EXPORT bool untaintRegister(const triton::arch::Register& reg);

          //! Abstract union tainting.
          TRITON_EXPORT bool taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

          //! Taints MemoryImmediate with union. Returns true if the memDst is TAINTED.
          TRITON_EXPORT bool taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::Immediate& imm);

          //! Taints MemoryMemory with union. Returns true if the memDst or memSrc are TAINTED.
          TRITON_EXPORT bool taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints MemoryRegister with union. Returns true if the memDst or regSrc are TAINTED.
          TRITON_EXPORT bool taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Taints RegisterImmediate with union. Returns true if the regDst is TAINTED.
          TRITON_EXPORT bool taintUnion(const triton::arch::Register& regDst, const triton::arch::Immediate& imm);

          //! Taints RegisterMemory with union. Returns true if the regDst or memSrc are TAINTED.
          TRITON_EXPORT bool taintUnion(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints RegisterRegister with union. Returns true if the regDst or regSrc are TAINTED.
          TRITON_EXPORT bool taintUnion(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

          //! Abstract assignment tainting.
          TRITON_EXPORT bool taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

          //! Taints MemoryImmediate with assignment. Returns always false.
          TRITON_EXPORT bool taintAssignment(const triton::arch::MemoryAccess& memDst,  const triton::arch::Immediate& imm);

          //! Taints MemoryMemory with assignment. Returns true if the memDst is tainted.
          TRITON_EXPORT bool taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints MemoryRegister with assignment. Returns true if the memDst is tainted.
          TRITON_EXPORT bool taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Taints RegisterImmediate with assignment. Returns always false.
          TRITON_EXPORT bool taintAssignment(const triton::arch::Register& regDst,  const triton::arch::Immediate& imm);

          //! Taints RegisterMemory with assignment. Returns true if the regDst is tainted.
          TRITON_EXPORT bool taintAssignment(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints RegisterRegister with assignment. Returns true if the regDst is tainted.
          TRITON_EXPORT bool taintAssignment(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

        private:
          //! Spreads MemoryImmediate with union.
          bool unionMemoryImmediate(const triton::arch::MemoryAccess& memDst);

          //! Spreads MemoryMemory with union.
          bool unionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Spreads MemoryRegister with union.
          bool unionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Spreads RegisterImmediate with union.
          bool unionRegisterImmediate(const triton::arch::Register& regDst);

          //! Spreads RegisterMemory with union.
          bool unionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Spreads RegisterRegister with union.
          bool unionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

          //! Spreads MemoryImmediate with assignment.
          bool assignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst);

          //! Spreads MemoryMemory with assignment.
          bool assignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Spreads MemoryRegister with assignment.
          bool assignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Spreads RegisterImmediate with assignment.
          bool assignmentRegisterImmediate(const triton::arch::Register& regDst);

          //! Spreads RegisterMemory with assignment.
          bool assignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Spreads RegisterRegister with assignment.
          bool assignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);
      };

    /*! @} End of taint namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* !__TRITON_TAINTENGINE_H__ */
