//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/taintEngine.hpp>



/*! \page engine_Taint_page Taint Engine
    \brief [**internal**] All information about the taint engine.

\tableofcontents

\section engine_Taint_description Description
<hr>

The purpose of dynamic taint analysis is to track the information flow from the
sources (usually user inputs) to the targets (such as control-flow value). It
is thus capable of analyzing which region of the memory and registers are
controllable by user inputs, which enables a further inspection of security
properties such as whether the control-flow values can be *infected* by user
inputs to allow control-flow hijacking.

A taint policy typically consists of the following three parts:

1) taint introduction rules
2) taint propagation rules
3) taint checking rules

The `libtriton`'s `TaintEngine` implements an architecture-independent **tag
propagation rules** while providing APIs for the taint introduction and taint
checking, enabling users to define their own taint policy. We currently
implement the semantics of x86 ISA only, but the core propagation rules can be
extended to other ISAs as well.


\section engine_Taint_over_approximation An Over-Approximation
<hr>

When implementing the taint propagation rules, there are three implementation
choices, each with accuracy-performance trade-offs.

- Over-approximation
- Precise-approximation
- Under-approximation

Triton currently implements an **over-approximation**, which has the following
advantages over precise-approximation:

- Easy to implement.
- Low runtime overhead.
- Consumes little memory.

An over-approximation is also more suitable in the bit-level granularity as
illustrated in the following scenario:

`e.g`: Imagine this 16-bits register `[x-x-x---x-xx-x-x]` where `x` are bits
that the user can control and `-` bits that the user cannot control. This
state of register is setup like that due to arithmetic operations but may be
something else with a different input value. In this case, it's not useful
to know what bits are controllable by the user because they will probably
change with another input value. In this case, using a **perfect-approximation**
or an **under-approximation** is **not useful**. What we want is only knowing
what values can hold this register according to the input.


\subsection engine_Taint_precision_vs_performance Precision with the Cost in Performance

An over-approximation may sacrifice the precision for the sake of
simplicity and performance. Let's look at the following ASM code.

~~~~~~~~~~~~~{.asm}
mov ax, 0x1122                ; RAX is untainted
mov al, byte ptr [user_input] ; RAX is tainted
cmp ah, 0x99                  ; can we control this comparison?
~~~~~~~~~~~~~

Under our current over-approximation, the taint engine will raise a false
positive (that says the `ah` is tainted while it actually is not) for this
particular example, while only the seven bits of `RAX` (`RAX[7..0]`) is tainted
while the other bits (`RAX[63..8]`) are not.

This imprecision may raise excessively extraneous false positive on a big
problem and make the tool totally useless in solving real problems. Let's
consider a scenario when an attacker is developing an exploit of an executable.
In this scenario, what the attacker wants to know is if a register at certain
program location can be controlled by himself, and furthermore, to what values
the register can be manipulated to hold. An over-approximation method including
the dynamic taint analysis is not capable of giving him/her such elaborate
information there are so many instructions which can manipulate a register at
any given program location.

In such situations, you can harness the power of symbolic execution by querying
a model at a program point. This is a much pricier operation to perform than
over-approximating dynamic taint analysis, but one can gain the precision while
paying the cost of performance.

This is why Triton uses **symbolic execution for precision** and an
over-approximated tainting to know if we can ask a model to the SMT solver - by
asking a model, we can query the solver and check if the symbolic variables are
controllable by the user input.

*/



namespace triton {
  namespace engines {
    namespace taint {

      TaintEngine::TaintEngine(triton::engines::symbolic::SymbolicEngine* symbolicEngine) {
        if (symbolicEngine == nullptr)
          throw triton::exceptions::TaintEngine("TaintEngine::TaintEngine(): The symbolicEngine TaintEngine cannot be null.");

        this->symbolicEngine = symbolicEngine;
        this->enableFlag     = true;
      }


      void TaintEngine::copy(const TaintEngine& other) {
        this->enableFlag       = other.enableFlag;
        this->symbolicEngine   = other.symbolicEngine;
        this->taintedMemory    = other.taintedMemory;
        this->taintedRegisters = other.taintedRegisters;
      }


      TaintEngine::TaintEngine(const TaintEngine& other) {
        this->copy(other);
      }


      TaintEngine::~TaintEngine() {
      }


      void TaintEngine::operator=(const TaintEngine& other) {
        this->copy(other);
      }


      bool TaintEngine::isEnabled(void) const {
        return this->enableFlag;
      }


      void TaintEngine::enable(bool flag) {
        this->enableFlag = flag;
      }


      /* Returns the tainted addresses */
      const std::set<triton::uint64>& TaintEngine::getTaintedMemory(void) const {
        return this->taintedMemory;
      }


      /* Returns the tainted registers */
      const std::set<triton::arch::Register>& TaintEngine::getTaintedRegisters(void) const {
        return this->taintedRegisters;
      }


      /* Returns true of false if the memory address is currently tainted */
      bool TaintEngine::isMemoryTainted(const triton::arch::MemoryAccess& mem) const {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        for (triton::uint32 index = 0; index < size; index++) {
          if (this->taintedMemory.find(addr+index) != this->taintedMemory.end())
            return TAINTED;
        }

        return !TAINTED;
      }


      /* Returns true of false if the address is currently tainted */
      bool TaintEngine::isMemoryTainted(triton::uint64 addr, triton::uint32 size) const {
        for (triton::uint32 index = 0; index < size; index++) {
          if (this->taintedMemory.find(addr+index) != this->taintedMemory.end())
            return TAINTED;
        }

        return !TAINTED;
      }


      /* Returns true of false if the register is currently tainted */
      bool TaintEngine::isRegisterTainted(const triton::arch::Register& reg) const {
        triton::arch::Register parent = reg.getParent();

        if (this->taintedRegisters.find(parent) != this->taintedRegisters.end())
          return TAINTED;

        return !TAINTED;
      }


      /* Abstract taint verification. */
      bool TaintEngine::isTainted(const triton::arch::OperandWrapper& op) const {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return triton::engines::taint::UNTAINTED;
          case triton::arch::OP_MEM: return this->isMemoryTainted(op.getConstMemory());
          case triton::arch::OP_REG: return this->isRegisterTainted(op.getConstRegister());
          default:
            throw triton::exceptions::TaintEngine("TaintEngine::isTainted(): Invalid operand.");
        }
      }


      /* Taint the register */
      bool TaintEngine::taintRegister(const triton::arch::Register& reg) {
        triton::arch::Register parent = reg.getParent();

        if (!this->isEnabled())
          return this->isRegisterTainted(parent);
        this->taintedRegisters.insert(parent);

        return TAINTED;
      }


      /* Untaint the register */
      bool TaintEngine::untaintRegister(const triton::arch::Register& reg) {
        triton::arch::Register parent = reg.getParent();

        if (!this->isEnabled())
          return this->isRegisterTainted(parent);
        this->taintedRegisters.erase(parent);

        return !TAINTED;
      }


      /* Sets the flag (taint or untaint) to an abstract operand (Register or Memory). */
      bool TaintEngine::setTaint(const triton::arch::OperandWrapper& op, bool flag) {
        switch (op.getType()) {
          case triton::arch::OP_IMM: return triton::engines::taint::UNTAINTED;
          case triton::arch::OP_MEM: return this->setTaintMemory(op.getConstMemory(), flag);
          case triton::arch::OP_REG: return this->setTaintRegister(op.getConstRegister(), flag);
          default:
            throw triton::exceptions::TaintEngine("TaintEngine::setTaint(): Invalid operand.");
        }
      }


      /* Sets the flag (taint or untaint) to a memory. */
      bool TaintEngine::setTaintMemory(const triton::arch::MemoryAccess& mem, bool flag) {
        if (!this->isEnabled())
          return this->isMemoryTainted(mem);

        if (flag == TAINTED)
          this->taintMemory(mem);

        else if (flag == !TAINTED)
          this->untaintMemory(mem);

        return flag;
      }


      /* Sets the flag (taint or untaint) to a register. */
      bool TaintEngine::setTaintRegister(const triton::arch::Register& reg, bool flag) {
        triton::arch::Register parent = reg.getParent();

        if (!this->isEnabled())
          return this->isRegisterTainted(parent);

        if (flag == TAINTED)
          this->taintRegister(parent);

        else if (flag == !TAINTED)
          this->untaintRegister(parent);

        return flag;
      }


      /* Taint the memory */
      bool TaintEngine::taintMemory(const triton::arch::MemoryAccess& mem) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        if (!this->isEnabled())
          return this->isMemoryTainted(mem);

        for (triton::uint32 index = 0; index < size; index++)
          this->taintedMemory.insert(addr+index);

        return TAINTED;
      }


      /* Taint the address */
      bool TaintEngine::taintMemory(triton::uint64 addr) {
        if (!this->isEnabled())
          return this->isMemoryTainted(addr);
        this->taintedMemory.insert(addr);
        return TAINTED;
      }


      /* Untaint the memory */
      bool TaintEngine::untaintMemory(const triton::arch::MemoryAccess& mem) {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        if (!this->isEnabled())
          return this->isMemoryTainted(mem);

        for (triton::uint32 index = 0; index < size; index++)
          this->taintedMemory.erase(addr+index);

        return !TAINTED;
      }


      /* Untaint the address */
      bool TaintEngine::untaintMemory(triton::uint64 addr) {
        if (!this->isEnabled())
          return this->isMemoryTainted(addr);
        this->taintedMemory.erase(addr);
        return !TAINTED;
      }


      /* Abstract union tainting */
      bool TaintEngine::taintUnion(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2) {
        triton::uint32 t1 = op1.getType();
        triton::uint32 t2 = op2.getType();

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
          return this->taintUnionMemoryImmediate(op1.getConstMemory());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
          return this->taintUnionMemoryMemory(op1.getConstMemory(), op2.getConstMemory());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
          return this->taintUnionMemoryRegister(op1.getConstMemory(), op2.getConstRegister());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
          return this->taintUnionRegisterImmediate(op1.getConstRegister());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
          return this->taintUnionRegisterMemory(op1.getConstRegister(), op2.getConstMemory());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
          return this->taintUnionRegisterRegister(op1.getConstRegister(), op2.getConstRegister());

        throw triton::exceptions::TaintEngine("TaintEngine::taintUnion(): Invalid operands.");
      }


      /* Abstract assignment tainting */
      bool TaintEngine::taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2) {
        triton::uint32 t1 = op1.getType();
        triton::uint32 t2 = op2.getType();

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
          return this->taintAssignmentMemoryImmediate(op1.getConstMemory());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
          return this->taintAssignmentMemoryMemory(op1.getConstMemory(), op2.getConstMemory());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
          return this->taintAssignmentMemoryRegister(op1.getConstMemory(), op2.getConstRegister());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
          return this->taintAssignmentRegisterImmediate(op1.getConstRegister());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
          return this->taintAssignmentRegisterMemory(op1.getConstRegister(), op2.getConstMemory());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
          return this->taintAssignmentRegisterRegister(op1.getConstRegister(), op2.getConstRegister());

        throw triton::exceptions::TaintEngine("TaintEngine::taintAssignment(): Invalid operands.");
      }


      bool TaintEngine::taintUnionMemoryImmediate(const triton::arch::MemoryAccess& memDst) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->unionMemoryImmediate(memDst);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          triton::usize byteId = this->symbolicEngine->getSymbolicMemoryId(memAddrDst + i);
          if (byteId == triton::engines::symbolic::UNSET)
            continue;
          triton::engines::symbolic::SymbolicExpression* byte = this->symbolicEngine->getSymbolicExpressionFromId(byteId);
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintUnionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint64 memAddrSrc = memSrc.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->unionMemoryMemory(memDst, memSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          triton::usize byteId = this->symbolicEngine->getSymbolicMemoryId(memAddrDst + i);
          if (byteId == triton::engines::symbolic::UNSET)
            continue;
          triton::engines::symbolic::SymbolicExpression* byte = this->symbolicEngine->getSymbolicExpressionFromId(byteId);
          byte->isTainted = this->isMemoryTainted(memAddrDst + i) | this->isMemoryTainted(memAddrSrc + i);
        }

        return flag;
      }


      bool TaintEngine::taintUnionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->unionMemoryRegister(memDst, regSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          triton::usize byteId = this->symbolicEngine->getSymbolicMemoryId(memAddrDst + i);
          if (byteId == triton::engines::symbolic::UNSET)
            continue;
          triton::engines::symbolic::SymbolicExpression* byte = this->symbolicEngine->getSymbolicExpressionFromId(byteId);
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintUnionRegisterImmediate(const triton::arch::Register& regDst) {
        return this->unionRegisterImmediate(regDst);
      }


      bool TaintEngine::taintUnionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
        return this->unionRegisterMemory(regDst, memSrc);
      }


      bool TaintEngine::taintUnionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
        return this->unionRegisterRegister(regDst, regSrc);
      }


      bool TaintEngine::taintAssignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->assignmentMemoryImmediate(memDst);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          triton::usize byteId = this->symbolicEngine->getSymbolicMemoryId(memAddrDst + i);
          if (byteId == triton::engines::symbolic::UNSET)
            continue;
          triton::engines::symbolic::SymbolicExpression* byte = this->symbolicEngine->getSymbolicExpressionFromId(byteId);
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintAssignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint64 memAddrSrc = memSrc.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->assignmentMemoryMemory(memDst, memSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          triton::usize byteId = this->symbolicEngine->getSymbolicMemoryId(memAddrDst + i);
          if (byteId == triton::engines::symbolic::UNSET)
            continue;
          triton::engines::symbolic::SymbolicExpression* byte = this->symbolicEngine->getSymbolicExpressionFromId(byteId);
          byte->isTainted = this->isMemoryTainted(memAddrSrc + i);
        }

        return flag;
      }


      bool TaintEngine::taintAssignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->assignmentMemoryRegister(memDst, regSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          triton::usize byteId = this->symbolicEngine->getSymbolicMemoryId(memAddrDst + i);
          if (byteId == triton::engines::symbolic::UNSET)
            continue;
          triton::engines::symbolic::SymbolicExpression* byte = this->symbolicEngine->getSymbolicExpressionFromId(byteId);
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintAssignmentRegisterImmediate(const triton::arch::Register& regDst) {
        return this->assignmentRegisterImmediate(regDst);
      }


      bool TaintEngine::taintAssignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
        return this->assignmentRegisterMemory(regDst, memSrc);
      }


      bool TaintEngine::taintAssignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
        return this->assignmentRegisterRegister(regDst, regSrc);
      }


      /* reg <- reg  */
      bool TaintEngine::assignmentRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isRegisterTainted(regSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        this->untaintRegister(regDst);
        return !TAINTED;
      }


      /* reg <- imm  */
      bool TaintEngine::assignmentRegisterImmediate(const triton::arch::Register& regDst) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);
        this->untaintRegister(regDst);
        return !TAINTED;
      }


      /* reg <- mem */
      bool TaintEngine::assignmentRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isMemoryTainted(memSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        this->untaintRegister(regDst);
        return !TAINTED;
      }


      /* mem <- mem  */
      bool TaintEngine::assignmentMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
        bool isTainted          = !TAINTED;
        triton::uint32 readSize = memSrc.getSize();
        triton::uint64 addrSrc  = memSrc.getAddress();
        triton::uint64 addrDst  = memDst.getAddress();

        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        for (triton::uint32 offset = 0; offset < readSize; offset++) {
          if (this->isMemoryTainted(addrSrc+offset)) {
            this->taintMemory(addrDst+offset);
            isTainted = TAINTED;
          }
          else
            this->untaintMemory(addrDst+offset);
        }

        return isTainted;
      }


      /* mem <- imm  */
      bool TaintEngine::assignmentMemoryImmediate(const triton::arch::MemoryAccess& memDst) {
        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);
        this->untaintMemory(memDst);
        return !TAINTED;
      }


      /* mem <- reg  */
      bool TaintEngine::assignmentMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
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


      /* reg U imm */
      bool TaintEngine::unionRegisterImmediate(const triton::arch::Register& regDst) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);
        return this->isRegisterTainted(regDst);
      }


      /* reg U reg */
      bool TaintEngine::unionRegisterRegister(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isRegisterTainted(regSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        return this->isRegisterTainted(regDst);
      }


      /* mem U mem */
      bool TaintEngine::unionMemoryMemory(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
        bool tainted             = !TAINTED;
        triton::uint32 writeSize = memDst.getSize();
        triton::uint64 addrDst   = memDst.getAddress();
        triton::uint64 addrSrc   = memSrc.getAddress();

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


      /* reg U mem */
      bool TaintEngine::unionRegisterMemory(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
        if (!this->isEnabled())
          return this->isRegisterTainted(regDst);

        if (this->isMemoryTainted(memSrc)) {
          this->taintRegister(regDst);
          return TAINTED;
        }

        return this->isRegisterTainted(regDst);
      }


      /* mem U imm */
      bool TaintEngine::unionMemoryImmediate(const triton::arch::MemoryAccess& memDst) {
        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        if (this->isMemoryTainted(memDst)) {
          return TAINTED;
        }

        return !TAINTED;
      }


      /* mem U reg */
      bool TaintEngine::unionMemoryRegister(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
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

