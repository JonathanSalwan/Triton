//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <api.hpp>
#include <taintEngine.hpp>



/*! \page engine_Taint_page Taint Engine
    \brief [**internal**] All information about the taint engine.

\tableofcontents

\section engine_Taint_description Description
<hr>

Taint analysis is used to know at each program point what part of memory
and register are controllable by the user input. There is three kinds of
taint granularity but an infinite number of ways to implement this analysis:

- Over-approximation
- Perfect-approximation
- Under-approximation

Triton uses an **over-approximation** and we will describe why.

\section engine_Taint_over_approximation An Over-Approximation
<hr>

With an **over-approximation**, we lose precision and we may provide false
positives. Example:

~~~~~~~~~~~~~{.asm}
mov ax, 0x1122                ; RAX is untainted
mov al, byte ptr [user_input] ; RAX is tainted
cmp ah, 0x99                  ; can we control this comparison?
~~~~~~~~~~~~~

If we ask to the taint engine if we can control the comparison, it will say
`YES` because `RAX` is tagged has tainted even if it's false. Actually,
`RAX[63..8]` is not tainted but RAX[7..0] is.

The only advantages of an **over-approximation** are:

- Easy to implement
- No cost of time
- No cost of RAM

This method is destructive on a big program, and so, totally useless for an
analyst. An analyst wants precisions even if this is not all possibilities.
Then, why an analyst may want to know if a register is tainted?

In exploit development, what the user wants in reality is knowing if a register
is controllable by himself and knowing what values can hold this register at
specific program point. Taint analysis (any over-approximation you choose)
cannot give you this kind of information. A lots of instructions have an
influence on the value that can hold a register. (Path conditions, arithmetic
operations, ...)

\subsection engine_Taint_big_quesiton The big question is: How can we gain time without losing precision?

Applying a symbolic execution and asking a model at each program point to know
if a register is controllable or not is pretty expensive. Therefore, we use an
<b>over-approximation</b> to fix the loss of time and if a register is tainted,
we ask a model for the precision.

`e.g`: Imagine this 16-bits register `[x-x-x---x-xx-x-x]` where `x` are bits
that the user can control and `-` bits that the user cannot control. This
state of register is setup like that due to arithmetic operations but may be
something else with a different input value. In this case, it's not useful
to know what bits are controllable by the user because they will probably
change with another input value. In this case, using a **perfect-approximation**
or an **under-approximation** is **not useful**. What we want is only knowing
what values can hold this register according to the input.

That's why Triton uses **symbolic execution for precision** and an over-approximated
tainting to know if we can ask a model to the SMT solver - Asking a model means that
the symbolic variables are controllable by the user input.

*/



namespace triton {
  namespace engines {
    namespace taint {

      TaintEngine::TaintEngine() {
        triton::api.checkArchitecture();
        this->numberOfRegisters = triton::api.cpuNumberOfRegisters();
        this->taintedRegisters  = new triton::uint8[this->numberOfRegisters]();
        this->enableFlag  = true;

        if (!this->taintedRegisters)
          throw std::invalid_argument("TaintEngine::TaintEngine(): No enough memory.");

        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->taintedRegisters[i] = !TAINTED;
      }


      void TaintEngine::init(const TaintEngine& other) {
        triton::api.checkArchitecture();
        this->numberOfRegisters = other.numberOfRegisters;
        this->taintedRegisters  = new triton::uint8[this->numberOfRegisters]();
        this->enableFlag  = other.enableFlag;

        if (!this->taintedRegisters)
          throw std::invalid_argument("TaintEngine::TaintEngine(): No enough memory.");

        for (triton::uint32 i = 0; i < this->numberOfRegisters; i++)
          this->taintedRegisters[i] = other.taintedRegisters[i];

        this->taintedAddresses = other.taintedAddresses;
      }


      TaintEngine::TaintEngine(const TaintEngine& copy) {
        init(copy);
      }


      TaintEngine::~TaintEngine() {
        delete[] this->taintedRegisters;
      }


      void TaintEngine::operator=(const TaintEngine& other) {
        delete[] this->taintedRegisters;
        init(other);
      }


      bool TaintEngine::isEnabled(void) const {
        return this->enableFlag;
      }


      void TaintEngine::enable(bool flag) {
        this->enableFlag = flag;
      }


      /* Returns true of false if the memory address is currently tainted */
      bool TaintEngine::isMemoryTainted(const triton::arch::MemoryOperand& mem) const {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        for (triton::uint32 index = 0; index < size; index++) {
          if (this->taintedAddresses.find(addr+index) != this->taintedAddresses.end())
            return TAINTED;
        }
        return !TAINTED;
      }


      /* Returns true of false if the address is currently tainted */
      bool TaintEngine::isMemoryTainted(triton::__uint addr, triton::uint32 size) const {
        for (triton::uint32 index = 0; index < size; index++) {
          if (this->taintedAddresses.find(addr+index) != this->taintedAddresses.end())
            return TAINTED;
        }
        return !TAINTED;
      }


      /* Returns true of false if the register is currently tainted */
      bool TaintEngine::isRegisterTainted(const triton::arch::RegisterOperand& reg) const {
        triton::uint32 parentId = reg.getParent().getId();
        return this->taintedRegisters[parentId];
      }


      /* Taint the register */
      bool TaintEngine::taintRegister(const triton::arch::RegisterOperand& reg) {
        triton::uint32 parentId = reg.getParent().getId();
        if (this->isEnabled())
          this->taintedRegisters[parentId] = TAINTED;
        return this->taintedRegisters[parentId];
      }


      /* Set the taint on memory */
      bool TaintEngine::setTaintMemory(const triton::arch::MemoryOperand& mem, bool flag) {
        if (!this->isEnabled())
          return this->isMemoryTainted(mem);

        if (flag == TAINTED)
          this->taintMemory(mem);

        else if (flag == !TAINTED)
          this->untaintMemory(mem);

        return flag;
      }


      /* Set the taint on register */
      bool TaintEngine::setTaintRegister(const triton::arch::RegisterOperand& reg, bool flag) {
        triton::uint32 parentId = reg.getParent().getId();
        if (this->isEnabled())
          this->taintedRegisters[parentId] = flag;
        return this->taintedRegisters[parentId];
      }


      /* Untaint the register */
      bool TaintEngine::untaintRegister(const triton::arch::RegisterOperand& reg) {
        triton::uint32 parentId = reg.getParent().getId();
        if (this->isEnabled())
          this->taintedRegisters[parentId] = !TAINTED;
        return this->taintedRegisters[parentId];
      }


      /* Taint the memory */
      bool TaintEngine::taintMemory(const triton::arch::MemoryOperand& mem) {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        if (!this->isEnabled())
          return this->isMemoryTainted(mem);

        for (triton::uint32 index = 0; index < size; index++)
          this->taintedAddresses[addr+index] = TAINTED;

        return TAINTED;
      }


      /* Taint the address */
      bool TaintEngine::taintMemory(triton::__uint addr) {
        if (this->isEnabled())
          this->taintedAddresses[addr] = TAINTED;
        return this->taintedAddresses[addr];
      }


      /* Untaint the memory */
      bool TaintEngine::untaintMemory(const triton::arch::MemoryOperand& mem) {
        triton::__uint addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        if (!this->isEnabled())
          return this->isMemoryTainted(mem);

        for (triton::uint32 index = 0; index < size; index++)
          this->taintedAddresses.erase(addr+index);

        return !TAINTED;
      }


      /* Untaint the address */
      bool TaintEngine::untaintMemory(triton::__uint addr) {
        if (!this->isEnabled())
          return this->isMemoryTainted(addr);
        this->taintedAddresses.erase(addr);
        return !TAINTED;
      }


      /*
       * Spread the taint in regDst if regSrc is tainted.
       * Returns true if a spreading occurs otherwise returns false.
       */
      bool TaintEngine::assignmentRegisterRegister(const triton::arch::RegisterOperand& regDst, const triton::arch::RegisterOperand& regSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isRegisterTainted(regSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        this->untaintRegister(regDst);
        return !TAINTED;
      }


      /*
       * Untaint the regDst.
       * Returns false.
       */
      bool TaintEngine::assignmentRegisterImmediate(const triton::arch::RegisterOperand& regDst) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);
        this->untaintRegister(regDst);
        return !TAINTED;
      }


      /*
       * Spread the taint in regDst if memSrc is tainted.
       * Returns true if a spreading occurs otherwise returns false.
       */
      bool TaintEngine::assignmentRegisterMemory(const triton::arch::RegisterOperand& regDst, const triton::arch::MemoryOperand& memSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isMemoryTainted(memSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        this->untaintRegister(regDst);
        return !TAINTED;
      }


      /*
       * Spread the taint in memDst if memSrc is tainted.
       * Returns true if a spreading occurs otherwise returns false.
       */
      bool TaintEngine::assignmentMemoryMemory(const triton::arch::MemoryOperand& memDst, const triton::arch::MemoryOperand& memSrc) {
        bool isTainted          = !TAINTED;
        triton::uint32 readSize = memSrc.getSize();
        triton::__uint addrSrc  = memSrc.getAddress();
        triton::__uint addrDst  = memDst.getAddress();

        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        for (triton::uint32 offset = 0; offset < readSize; offset++) {
          if (this->isMemoryTainted(addrSrc+offset)) {
            this->taintMemory(addrDst+offset);
            isTainted = TAINTED;
          }
        }
        return isTainted;
      }


      /*
       * Untaint the memDst.
       * Returns false.
       */
      bool TaintEngine::assignmentMemoryImmediate(const triton::arch::MemoryOperand& memDst) {
        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);
        this->untaintMemory(memDst);
        return !TAINTED;
      }


      /*
       * Spread the taint in memDst if regSrc is tainted.
       * Returns true if a spreading occurs otherwise returns false.
       */
      bool TaintEngine::assignmentMemoryRegister(const triton::arch::MemoryOperand& memDst, const triton::arch::RegisterOperand& regSrc) {
        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        /* Check source */
        if (this->isRegisterTainted(regSrc)) {
          this->taintMemory(memDst);
          return TAINTED;
        }

        /* Spread destination */
        this->untaintMemory(memDst);
        return !TAINTED;
      }


      /*
       * If the reg is tainted, we returns true to taint the SE.
       */
      bool TaintEngine::unionRegisterImmediate(const triton::arch::RegisterOperand& regDst) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);
        return this->isRegisterTainted(regDst);
      }


      /*
       * If the RegSrc is tainted we taint the regDst, otherwise
       * we check if regDst is tainted and returns the status.
       */
      bool TaintEngine::unionRegisterRegister(const triton::arch::RegisterOperand& regDst, const triton::arch::RegisterOperand& regSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isRegisterTainted(regSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        return this->isRegisterTainted(regDst);
      }


      /*
       * If the MemSrc is tainted we taint the memDst, otherwise
       * we check if memDst is tainted and returns the status.
       */
      bool TaintEngine::unionMemoryMemory(const triton::arch::MemoryOperand& memDst, const triton::arch::MemoryOperand& memSrc) {
        bool tainted             = !TAINTED;
        triton::uint32 writeSize = memDst.getSize();
        triton::__uint addrDst   = memDst.getAddress();
        triton::__uint addrSrc   = memSrc.getAddress();

        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        /* Check source */
        for (triton::uint32 offset = 0; offset < writeSize; offset++) {
          if (this->isMemoryTainted(addrSrc+offset)) {
            this->taintMemory(addrDst+offset);
            tainted = TAINTED;
          }
        }

        /* Check destination */
        if (this->isMemoryTainted(memDst)) {
          return TAINTED;
        }

        return tainted;
      }


      /*
       * If the Mem is tainted we taint the regDst, otherwise
       * we check if regDst is tainted and returns the status.
       */
      bool TaintEngine::unionRegisterMemory(const triton::arch::RegisterOperand& regDst, const triton::arch::MemoryOperand& memSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isMemoryTainted(memSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        return this->isRegisterTainted(regDst);
      }


      /* Returns true if the memDst is tainted. */
      bool TaintEngine::unionMemoryImmediate(const triton::arch::MemoryOperand& memDst) {
        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        if (this->isMemoryTainted(memDst)) {
          return TAINTED;
        }

        return !TAINTED;
      }


      /* If regSrc is tainted, we taint the memDst, then if the memDst is tainted we returns true. */
      bool TaintEngine::unionMemoryRegister(const triton::arch::MemoryOperand& memDst, const triton::arch::RegisterOperand& regSrc) {
        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        if (this->isRegisterTainted(regSrc)) {
          this->taintMemory(memDst);
          return TAINTED;
        }

        if (this->isMemoryTainted(memDst))
          return TAINTED;

        return !TAINTED;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */

