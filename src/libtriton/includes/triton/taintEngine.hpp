//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TAINTENGINE_H
#define TRITON_TAINTENGINE_H

#include <set>

#include <triton/memoryAccess.hpp>
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
          //! Symbolic Engine API
          triton::engines::symbolic::SymbolicEngine* symbolicEngine;

        protected:
          //! Defines if the taint engine is enabled or disabled.
          bool enableFlag;

          //! The set of tainted addresses.
          std::set<triton::uint64> taintedMemory;

          //! The set of tainted registers. Currently it is an over approximation of the taint.
          std::set<triton::arch::Register> taintedRegisters;

          //! Copies a TaintEngine.
          void copy(const TaintEngine& other);

        public:
          //! Constructor.
          TaintEngine(triton::engines::symbolic::SymbolicEngine* symbolicEngine);

          //! Constructor by copy.
          TaintEngine(const TaintEngine& copy);

          //! Destructor.
          virtual ~TaintEngine();

          //! Copies a TaintEngine.
          void operator=(const TaintEngine& other);

          //! Enables or disables the taint engine.
          void enable(bool flag);

          //! Returns the tainted addresses.
          const std::set<triton::uint64>& getTaintedMemory(void) const;

          //! Returns the tainted registers.
          const std::set<triton::arch::Register>& getTaintedRegisters(void) const;

          //! Returns true if the taint engine is enabled.
          bool isEnabled(void) const;

          //! Returns true if the addr is tainted.
          bool isMemoryTainted(triton::uint64 addr, triton::uint32 size=1) const;

          //! Returns true if the memory is tainted.
          bool isMemoryTainted(const triton::arch::MemoryAccess& mem) const;

          //! Returns true if the register is tainted.
          bool isRegisterTainted(const triton::arch::Register& reg) const;

          //! Abstract taint verification. Returns true if the operand is tainted.
          bool isTainted(const triton::arch::OperandWrapper& op) const;

          //! Sets the flag (taint or untaint) to an abstract operand (Register or Memory).
          bool setTaint(const triton::arch::OperandWrapper& op, bool flag);

          //! Sets the flag (taint or untaint) to a memory.
          bool setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag);

          //! Sets the flag (taint or untaint) to a register.
          bool setTaintRegister(const triton::arch::Register& reg, bool flag);

          //! Taints an address. Returns TAINTED if the address has been tainted correctly. Otherwise it returns the last defined state.
          bool taintMemory(triton::uint64 addr);

          //! Taints a memory. Returns TAINTED if the memory has been tainted correctly. Otherwise it returns the last defined state.
          bool taintMemory(const triton::arch::MemoryAccess& mem);

          //! Taints a register. Returns TAINTED if the register has been tainted correctly. Otherwise it returns the last defined state.
          bool taintRegister(const triton::arch::Register& reg);

          //! Untaints an address. Returns !TAINTED if the address has been untainted correctly. Otherwise it returns the last defined state.
          bool untaintMemory(triton::uint64 addr);

          //! Untaints a memory. Returns !TAINTED if the memory has been untainted correctly. Otherwise it returns the last defined state.
          bool untaintMemory(const triton::arch::MemoryAccess& mem);

          //! Untaints a register. Returns !TAINTED if the register has been untainted correctly. Otherwise it returns the last defined state.
          bool untaintRegister(const triton::arch::Register& reg);

          //! Abstract union tainting.
          bool taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

          //! Abstract assignment tainting.
          bool taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2);

          //! Taints MemoryImmediate with union. Returns true if the memDst is TAINTED.
          bool taintUnionMemoryImmediate(const triton::arch::MemoryAccess& memDst);

          //! Taints MemoryMemory with union. Returns true if the memDst or memSrc are TAINTED.
          bool taintUnionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints MemoryRegister with union. Returns true if the memDst or regSrc are TAINTED.
          bool taintUnionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Taints RegisterImmediate with union. Returns true if the regDst is TAINTED.
          bool taintUnionRegisterImmediate(const triton::arch::Register& regDst);

          //! Taints RegisterMemory with union. Returns true if the regDst or memSrc are TAINTED.
          bool taintUnionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints RegisterRegister with union. Returns true if the regDst or regSrc are TAINTED.
          bool taintUnionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

          //! Taints MemoryImmediate with assignment. Returns always false.
          bool taintAssignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst);

          //! Taints MemoryMemory with assignment. Returns true if the memDst is tainted.
          bool taintAssignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints MemoryRegister with assignment. Returns true if the memDst is tainted.
          bool taintAssignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Taints RegisterImmediate with assignment. Returns always false.
          bool taintAssignmentRegisterImmediate(const triton::arch::Register& regDst);

          //! Taints RegisterMemory with assignment. Returns true if the regDst is tainted.
          bool taintAssignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints RegisterRegister with assignment. Returns true if the regDst is tainted.
          bool taintAssignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

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

