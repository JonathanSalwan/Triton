//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_TAINTENGINE_H
#define TRITON_TAINTENGINE_H

#include <set>

#include "memoryAccess.hpp"
#include "register.hpp"
#include "symbolicEngine.hpp"
#include "tritonTypes.hpp"



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

          //! Returns true if the taint engine is enabled.
          bool isEnabled(void) const;

          //! Enables or disables the taint engine.
          void enable(bool flag);

          //! Returns the tainted addresses.
          const std::set<triton::uint64>& getTaintedMemory(void) const;

          //! Returns the tainted registers.
          const std::set<triton::arch::Register>& getTaintedRegisters(void) const;

          //! Returns true if the addr is tainted.
          /*!
            \param addr the targeted address.
            \param size the access' size
          */
          bool isMemoryTainted(triton::uint64 addr, triton::uint32 size=1) const;

          //! Returns true if the memory is tainted.
          /*!
            \param mem the memory access.
          */
          bool isMemoryTainted(const triton::arch::MemoryAccess& mem) const;

          //! Returns true if the register is tainted.
          /*!
            \param reg the register operand.
          */
          bool isRegisterTainted(const triton::arch::Register& reg) const;

          //! Abstract taint verification.
          /*!
            \param op the abstract operand. Can be a register or a memory.
          */
          bool isTainted(const triton::arch::OperandWrapper& op) const;

          //! Sets the flag (taint) to an abstract operand (Register or Memory).
          /*!
            \param op the abstract operand. Can be a register or a memory.
          */
          bool setTaint(const triton::arch::OperandWrapper& op, bool flag);

          //! Sets memory flag.
          /*!
            \param mem the memory access.
            \param flag TAINTED or !TAINTED
          */
          bool setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag);

          //! Sets register flag.
          /*!
            \param reg the register operand.
            \param flag TAINTED or !TAINTED
          */
          bool setTaintRegister(const triton::arch::Register& reg, bool flag);

          //! Taints an address.
          /*!
            \param addr the targeted address.
            \return TAINTED if the address has been tainted correctly. Otherwise it returns the last defined state.
          */
          bool taintMemory(triton::uint64 addr);

          //! Taints a memory.
          /*!
            \param mem the memory access.
            \return TAINTED if the memory has been tainted correctly. Otherwise it returns the last defined state.
          */
          bool taintMemory(const triton::arch::MemoryAccess& mem);

          //! Taints a register.
          /*!
            \param reg the register operand.
            \return TAINTED if the register has been tainted correctly. Otherwise it returns the last defined state.
          */
          bool taintRegister(const triton::arch::Register& reg);

          //! Untaints an address.
          /*!
            \param addr the targeted address.
            \return !TAINTED if the address has been untainted correctly. Otherwise it returns the last defined state.
          */
          bool untaintMemory(triton::uint64 addr);

          //! Untaints a memory.
          /*!
            \param mem the memory access.
            \return !TAINTED if the memory has been untainted correctly. Otherwise it returns the last defined state.
          */
          bool untaintMemory(const triton::arch::MemoryAccess& mem);

          //! Untaints a register.
          /*!
            \param reg the register operand.
            \return !TAINTED if the register has been untainted correctly. Otherwise it returns the last defined state.
          */
          bool untaintRegister(const triton::arch::Register& reg);

          //! Taints MemoryImmediate with union.
          /*!
            \param memDst the memory destination.
            \return true if the memDst is TAINTED.
          */
          bool unionMemoryImmediate(const triton::arch::MemoryAccess& memDst);

          //! Taints MemoryMemory with union.
          /*!
            \param memDst the memory destination.
            \param memSrc the memory source.
            \return true if the memDst or memSrc are TAINTED.
          */
          bool unionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints MemoryRegister with union.
          /*!
            \param memDst the memory destination.
            \param regSrc the register source.
            \return true if the memDst or regSrc are TAINTED.
          */
          bool unionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Taints RegisterImmediate with union.
          /*!
            \param regDst the register source.
            \return true if the regDst is TAINTED.
          */
          bool unionRegisterImmediate(const triton::arch::Register& regDst);

          //! Taints RegisterMemory with union.
          /*!
            \param regDst the register destination.
            \param memSrc the memory source.
            \return true if the regDst or memSrc are TAINTED.
          */
          bool unionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints RegisterRegister with union.
          /*!
            \param regDst the register destination.
            \param regSrc the register source.
            \return true if the regDst or regSrc are TAINTED.
          */
          bool unionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);

          //! Taints MemoryImmediate with assignment.
          /*!
            \param memDst the memory destination.
            \return always false.
          */
          bool assignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst);

          //! Taints MemoryMemory with assignment.
          /*!
            \param memDst the memory destination.
            \param memSrc the memory source.
            \return true if the memDst is tainted.
          */
          bool assignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints MemoryRegister with assignment.
          /*!
            \param memDst the memory destination.
            \param regSrc the register source.
            \return true if the memDst is tainted.
          */
          bool assignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc);

          //! Taints RegisterImmediate with assignment.
          /*!
            \param regDst the register destination.
            \return always false.
          */
          bool assignmentRegisterImmediate(const triton::arch::Register& regDst);

          //! Taints RegisterMemory with assignment.
          /*!
            \param regDst the register destination.
            \param memSrc the memory source.
            \return true if the regDst is tainted.
          */
          bool assignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc);

          //! Taints RegisterRegister with assignment.
          /*!
            \param regDst the register destination.
            \param regSrc the register source.
            \return true if the regDst is tainted.
          */
          bool assignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc);
      };

    /*! @} End of taint namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* !__TRITON_TAINTENGINE_H__ */

