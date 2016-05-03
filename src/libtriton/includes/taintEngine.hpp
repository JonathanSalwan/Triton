//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_TAINTENGINE_H
#define TRITON_TAINTENGINE_H

#include <map>
#include <sstream>
#include <stdint.h>

#include "memoryOperand.hpp"
#include "registerOperand.hpp"
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Taint namespace
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

        protected:

          //! Enable / Disable flag.
          bool enableFlag;

          //! The map of tainted address.
          std::map<triton::__uint, bool> taintedAddresses;

          //! The number of register according to the CPU.
          triton::uint32 numberOfRegisters;

          //! Tainted registers. Currently this is an over approximation of the taint but a byte granularity can be used.
          triton::uint8  *taintedRegisters;

          //! Copies a TaintEngine.
          void init(const TaintEngine& other);


        public:
          //! Returns true if the taint engine is enabled.
          bool isEnabled(void) const;

          //! Enables or disables the taint engine.
          void enable(bool flag);

          //! Returns true if the addr is tainted.
          /*!
            \param addr the targeted address.
            \param size the access' size
          */
          bool isMemoryTainted(triton::__uint addr, triton::uint32 size=1) const;

          //! Returns true if the memory is tainted.
          /*!
            \param mem the memory operand.
          */
          bool isMemoryTainted(const triton::arch::MemoryOperand& mem) const;

          //! Returns true if the register is tainted.
          /*!
            \param reg the register operand.
          */
          bool isRegisterTainted(const triton::arch::RegisterOperand& reg) const;

          //! Sets memory flag.
          /*!
            \param mem the memory operand.
            \param flag TAINTED or !TAINTED
          */
          bool setTaintMemory(const triton::arch::MemoryOperand& mem, bool flag);

          //! Sets register flag.
          /*!
            \param reg the register operand.
            \param flag TAINTED or !TAINTED
          */
          bool setTaintRegister(const triton::arch::RegisterOperand& reg, bool flag);

          //! Taints an address.
          /*!
            \param addr the targeted address.
          */
          bool taintMemory(triton::__uint addr);

          //! Taints a memory.
          /*!
            \param mem the memory operand.
          */
          bool taintMemory(const triton::arch::MemoryOperand& mem);

          //! Taints a register.
          /*!
            \param reg the register operand.
          */
          bool taintRegister(const triton::arch::RegisterOperand& reg);

          //! Untaints an address.
          /*!
            \param addr the targeted address.
          */
          bool untaintMemory(triton::__uint addr);

          //! Untaints a memory.
          /*!
            \param mem the memory operand.
          */
          bool untaintMemory(const triton::arch::MemoryOperand& mem);

          //! Untaints a register.
          /*!
            \param reg the register operand.
          */
          bool untaintRegister(const triton::arch::RegisterOperand& reg);

          //! Taints MemoryImmediate with union.
          /*!
            \param memDst the memory destination.
            \return true if the memDst is TAINTED.
          */
          bool unionMemoryImmediate(const triton::arch::MemoryOperand& memDst);

          //! Taints MemoryMemory with union.
          /*!
            \param memDst the memory destination.
            \param memSrc the memory source.
            \return true if the memDst or memSrc are TAINTED.
          */
          bool unionMemoryMemory(const triton::arch::MemoryOperand& memDst, const triton::arch::MemoryOperand& memSrc);

          //! Taints MemoryRegister with union.
          /*!
            \param memDst the memory destination.
            \param regSrc the register source.
            \return true if the memDst or regSrc are TAINTED.
          */
          bool unionMemoryRegister(const triton::arch::MemoryOperand& memDst, const triton::arch::RegisterOperand& regSrc);

          //! Taints RegisterImmediate with union.
          /*!
            \param regDst the register source.
            \return true if the regDst is TAINTED.
          */
          bool unionRegisterImmediate(const triton::arch::RegisterOperand& regDst);

          //! Taints RegisterMemory with union.
          /*!
            \param regDst the register destination.
            \param memSrc the memory source.
            \return true if the regDst or memSrc are TAINTED.
          */
          bool unionRegisterMemory(const triton::arch::RegisterOperand& regDst, const triton::arch::MemoryOperand& memSrc);

          //! Taints RegisterRegister with union.
          /*!
            \param regDst the register destination.
            \param regSrc the register source.
            \return true if the regDst or regSrc are TAINTED.
          */
          bool unionRegisterRegister(const triton::arch::RegisterOperand& regDst, const triton::arch::RegisterOperand& regSrc);

          //! Taints MemoryImmediate with assignment.
          /*!
            \param memDst the memory destination.
            \return always false.
          */
          bool assignmentMemoryImmediate(const triton::arch::MemoryOperand& memDst);

          //! Taints MemoryMemory with assignment.
          /*!
            \param memDst the memory destination.
            \param memSrc the memory source.
            \return true if the memDst is tainted.
          */
          bool assignmentMemoryMemory(const triton::arch::MemoryOperand& memDst, const triton::arch::MemoryOperand& memSrc);

          //! Taints MemoryRegister with assignment.
          /*!
            \param memDst the memory destination.
            \param regSrc the register source.
            \return true if the memDst is tainted.
          */
          bool assignmentMemoryRegister(const triton::arch::MemoryOperand& memDst, const triton::arch::RegisterOperand& regSrc);

          //! Taints RegisterImmediate with assignment.
          /*!
            \param regDst the register destination.
            \return always false.
          */
          bool assignmentRegisterImmediate(const triton::arch::RegisterOperand& regDst);

          //! Taints RegisterMemory with assignment.
          /*!
            \param regDst the register destination.
            \param memSrc the memory source.
            \return true if the regDst is tainted.
          */
          bool assignmentRegisterMemory(const triton::arch::RegisterOperand& regDst, const triton::arch::MemoryOperand& memSrc);

          //! Taints RegisterRegister with assignment.
          /*!
            \param regDst the register destination.
            \param regSrc the register source.
            \return true if the regDst is tainted.
          */
          bool assignmentRegisterRegister(const triton::arch::RegisterOperand& regDst, const triton::arch::RegisterOperand& regSrc);

          //! Copies a TaintEngine.
          void operator=(const TaintEngine& other);

          //! Constructor.
          TaintEngine();

          //! Constructor by copy.
          TaintEngine(const TaintEngine& copy);

          //! Destructor.
          ~TaintEngine();
      };

    /*! @} End of taint namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* !__TRITON_TAINTENGINE_H__ */

