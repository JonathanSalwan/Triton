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
          triton::uint32 numberOfReg;

          //! Tainted registers. Currently this is an over approximation of the taint but a byte granularity can be used.
          triton::uint8  *taintedReg;

          //! Copies a TaintEngine.
          void init(const TaintEngine& other);


        public:
          //! Returns true if the taint engine is enabled.
          bool isEnabled(void);

          //! Enables or disables the taint engine.
          void enable(bool flag);

          //! Returns true if the addr is tainted.
          /*!
            \param addr the targeted address.
            \param size the access' size
          */
          bool isAddrTainted(triton::__uint addr, triton::uint32 size=1);

          //! Returns true if the memory is tainted.
          /*!
            \param mem the memory operand.
          */
          bool isMemTainted(triton::arch::MemoryOperand& mem);

          //! Returns true if the register is tainted.
          /*!
            \param reg the register operand.
          */
          bool isRegTainted(triton::arch::RegisterOperand& reg);

          //! Sets memory's flag.
          /*!
            \param mem the memory operand.
            \param flag TAINTED or !TAINTED
          */
          bool setTaintMem(triton::arch::MemoryOperand& mem, bool flag);

          //! Sets register's flag.
          /*!
            \param reg the register operand.
            \param flag TAINTED or !TAINTED
          */
          bool setTaintReg(triton::arch::RegisterOperand& reg, bool flag);

          //! Taints an address.
          /*!
            \param addr the targeted address.
          */
          bool taintAddr(triton::__uint addr);

          //! Taints a memory.
          /*!
            \param mem the memory operand.
          */
          bool taintMem(triton::arch::MemoryOperand& mem);

          //! Taints a register.
          /*!
            \param reg the register operand.
          */
          bool taintReg(triton::arch::RegisterOperand& reg);

          //! Untaints an address.
          /*!
            \param addr the targeted address.
          */
          bool untaintAddr(triton::__uint addr);

          //! Untaints a memory.
          /*!
            \param mem the memory operand.
          */
          bool untaintMem(triton::arch::MemoryOperand& mem);

          //! Untaints a register.
          /*!
            \param reg the register operand.
          */
          bool untaintReg(triton::arch::RegisterOperand& reg);

          //! Taints MemImm with union.
          /*!
            \param memDst the memory destination.
            \return true if the memDst is TAINTED.
          */
          bool unionMemImm(triton::arch::MemoryOperand& memDst);

          //! Taints MemMem with union.
          /*!
            \param memDst the memory destination.
            \param memSrc the memory source.
            \return true if the memDst or memSrc are TAINTED.
          */
          bool unionMemMem(triton::arch::MemoryOperand& memDst, triton::arch::MemoryOperand& memSrc);

          //! Taints MemReg with union.
          /*!
            \param memDst the memory destination.
            \param regSrc the register source.
            \return true if the memDst or regSrc are TAINTED.
          */
          bool unionMemReg(triton::arch::MemoryOperand& memDst, triton::arch::RegisterOperand& regSrc);

          //! Taints RegImm with union.
          /*!
            \param regDst the register source.
            \return true if the regDst is TAINTED.
          */
          bool unionRegImm(triton::arch::RegisterOperand& regDst);

          //! Taints RegMem with union.
          /*!
            \param regDst the register destination.
            \param memSrc the memory source.
            \return true if the regDst or memSrc are TAINTED.
          */
          bool unionRegMem(triton::arch::RegisterOperand& regDst, triton::arch::MemoryOperand& memSrc);

          //! Taints RegReg with union.
          /*!
            \param regDst the register destination.
            \param regSrc the register source.
            \return true if the regDst or regSrc are TAINTED.
          */
          bool unionRegReg(triton::arch::RegisterOperand& regDst, triton::arch::RegisterOperand& regSrc);

          //! Taints MemImm with assignment.
          /*!
            \param memDst the memory destination.
            \return always false.
          */
          bool assignmentMemImm(triton::arch::MemoryOperand& memDst);

          //! Taints MemMem with assignment.
          /*!
            \param memDst the memory destination.
            \param memSrc the memory source.
            \return true if the memDst is tainted.
          */
          bool assignmentMemMem(triton::arch::MemoryOperand& memDst, triton::arch::MemoryOperand& memSrc);

          //! Taints MemReg with assignment.
          /*!
            \param memDst the memory destination.
            \param regSrc the register source.
            \return true if the memDst is tainted.
          */
          bool assignmentMemReg(triton::arch::MemoryOperand& memDst, triton::arch::RegisterOperand& regSrc);

          //! Taints RegImm with assignment.
          /*!
            \param regDst the register destination.
            \return always false.
          */
          bool assignmentRegImm(triton::arch::RegisterOperand& regDst);

          //! Taints RegMem with assignment.
          /*!
            \param regDst the register destination.
            \param memSrc the memory source.
            \return true if the regDst is tainted.
          */
          bool assignmentRegMem(triton::arch::RegisterOperand& regDst, triton::arch::MemoryOperand& memSrc);

          //! Taints RegReg with assignment.
          /*!
            \param regDst the register destination.
            \param regSrc the register source.
            \return true if the regDst is tainted.
          */
          bool assignmentRegReg(triton::arch::RegisterOperand& regDst, triton::arch::RegisterOperand& regSrc);

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

