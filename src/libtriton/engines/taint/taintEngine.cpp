//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/taintEngine.hpp>



namespace triton {
  namespace engines {
    namespace taint {

      TaintEngine::TaintEngine(const triton::modes::SharedModes& modes, triton::engines::symbolic::SymbolicEngine* symbolicEngine, triton::arch::CpuInterface& cpu)
        : modes(modes),
          symbolicEngine(symbolicEngine),
          cpu(cpu),
          enableFlag(true) {

        if (this->symbolicEngine == nullptr)
          throw triton::exceptions::TaintEngine("TaintEngine::TaintEngine(): The symbolicEngine TaintEngine cannot be null.");
      }


      TaintEngine::TaintEngine(const TaintEngine& other)
        : modes(other.modes),
          cpu(other.cpu) {
        this->enableFlag       = other.enableFlag;
        this->symbolicEngine   = other.symbolicEngine;
        this->taintedMemory    = other.taintedMemory;
        this->taintedRegisters = other.taintedRegisters;
      }


      TaintEngine& TaintEngine::operator=(const TaintEngine& other) {
        this->cpu              = other.cpu;
        this->enableFlag       = other.enableFlag;
        this->modes            = other.modes;
        this->symbolicEngine   = other.symbolicEngine;
        this->taintedMemory    = other.taintedMemory;
        this->taintedRegisters = other.taintedRegisters;
        return *this;
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
      std::set<const triton::arch::Register*> TaintEngine::getTaintedRegisters(void) const {
        std::set<const triton::arch::Register*> res;

        for (auto id : this->taintedRegisters)
          res.insert(&this->cpu.getRegister(id));

        return res;
      }


      /* Returns true of false if the memory address is currently tainted */
      bool TaintEngine::isMemoryTainted(const triton::arch::MemoryAccess& mem, bool mode) const {
        triton::uint64 addr = mem.getAddress();
        triton::uint32 size = mem.getSize();

        for (triton::uint32 index = 0; index < size; index++) {
          if (this->taintedMemory.find(addr+index) != this->taintedMemory.end())
            return TAINTED;
        }

        /* Spread the taint through pointers if the mode is enabled */
        if (mode && this->modes->isModeEnabled(triton::modes::TAINT_THROUGH_POINTERS)) {
          if (this->isRegisterTainted(mem.getConstBaseRegister()))
            return TAINTED;
          if (this->isRegisterTainted(mem.getConstIndexRegister()))
            return TAINTED;
          if (this->isRegisterTainted(mem.getConstSegmentRegister()))
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
        if (this->taintedRegisters.find(reg.getParent()) != this->taintedRegisters.end())
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
        if (!this->isEnabled())
          return this->isRegisterTainted(reg);
        this->taintedRegisters.insert(reg.getParent());

        return TAINTED;
      }


      /* Untaint the register */
      bool TaintEngine::untaintRegister(const triton::arch::Register& reg) {
        if (!this->isEnabled())
          return this->isRegisterTainted(reg);
        this->taintedRegisters.erase(reg.getParent());

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
        if (!this->isEnabled())
          return this->isRegisterTainted(reg);

        if (flag == TAINTED)
          this->taintRegister(reg);

        else if (flag == !TAINTED)
          this->untaintRegister(reg);

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
          return this->taintUnion(op1.getConstMemory(), op2.getConstImmediate());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
          return this->taintUnion(op1.getConstMemory(), op2.getConstMemory());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
          return this->taintUnion(op1.getConstMemory(), op2.getConstRegister());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
          return this->taintUnion(op1.getConstRegister(), op2.getConstImmediate());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
          return this->taintUnion(op1.getConstRegister(), op2.getConstMemory());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
          return this->taintUnion(op1.getConstRegister(), op2.getConstRegister());

        throw triton::exceptions::TaintEngine("TaintEngine::taintUnion(): Invalid operands.");
      }


      /* Abstract assignment tainting */
      bool TaintEngine::taintAssignment(const triton::arch::OperandWrapper& op1, const triton::arch::OperandWrapper& op2) {
        triton::uint32 t1 = op1.getType();
        triton::uint32 t2 = op2.getType();

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_IMM)
          return this->taintAssignment(op1.getConstMemory(), op2.getConstImmediate());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_MEM)
          return this->taintAssignment(op1.getConstMemory(), op2.getConstMemory());

        if (t1 == triton::arch::OP_MEM && t2 == triton::arch::OP_REG)
          return this->taintAssignment(op1.getConstMemory(), op2.getConstRegister());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_IMM)
          return this->taintAssignment(op1.getConstRegister(), op2.getConstImmediate());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_MEM)
          return this->taintAssignment(op1.getConstRegister(), op2.getConstMemory());

        if (t1 == triton::arch::OP_REG && t2 == triton::arch::OP_REG)
          return this->taintAssignment(op1.getConstRegister(), op2.getConstRegister());

        throw triton::exceptions::TaintEngine("TaintEngine::taintAssignment(): Invalid operands.");
      }


      bool TaintEngine::taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::Immediate& imm) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->unionMemoryImmediate(memDst);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          const triton::engines::symbolic::SharedSymbolicExpression& byte = this->symbolicEngine->getSymbolicMemory(memAddrDst + i);
          if (byte == nullptr)
            continue;
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint64 memAddrSrc = memSrc.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->unionMemoryMemory(memDst, memSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          const triton::engines::symbolic::SharedSymbolicExpression& byte = this->symbolicEngine->getSymbolicMemory(memAddrDst + i);
          if (byte == nullptr)
            continue;
          byte->isTainted = this->isMemoryTainted(memAddrDst + i) | this->isMemoryTainted(memAddrSrc + i);
        }

        return flag;
      }


      bool TaintEngine::taintUnion(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->unionMemoryRegister(memDst, regSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          const triton::engines::symbolic::SharedSymbolicExpression& byte = this->symbolicEngine->getSymbolicMemory(memAddrDst + i);
          if (byte == nullptr)
            continue;
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintUnion(const triton::arch::Register& regDst, const triton::arch::Immediate& imm) {
        return this->unionRegisterImmediate(regDst);
      }


      bool TaintEngine::taintUnion(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
        return this->unionRegisterMemory(regDst, memSrc);
      }


      bool TaintEngine::taintUnion(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
        return this->unionRegisterRegister(regDst, regSrc);
      }


      bool TaintEngine::taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::Immediate& imm) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->assignmentMemoryImmediate(memDst);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          const triton::engines::symbolic::SharedSymbolicExpression& byte = this->symbolicEngine->getSymbolicMemory(memAddrDst + i);
          if (byte == nullptr)
            continue;
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::MemoryAccess& memSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint64 memAddrSrc = memSrc.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->assignmentMemoryMemory(memDst, memSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          const triton::engines::symbolic::SharedSymbolicExpression& byte = this->symbolicEngine->getSymbolicMemory(memAddrDst + i);
          if (byte == nullptr)
            continue;
          byte->isTainted = this->isMemoryTainted(memAddrSrc + i);
        }

        return flag;
      }


      bool TaintEngine::taintAssignment(const triton::arch::MemoryAccess& memDst, const triton::arch::Register& regSrc) {
        bool flag = triton::engines::taint::UNTAINTED;
        triton::uint64 memAddrDst = memDst.getAddress();
        triton::uint32 writeSize  = memDst.getSize();

        flag = this->assignmentMemoryRegister(memDst, regSrc);

        /* Taint each byte of reference expression */
        for (triton::uint32 i = 0; i != writeSize; i++) {
          const triton::engines::symbolic::SharedSymbolicExpression& byte = this->symbolicEngine->getSymbolicMemory(memAddrDst + i);
          if (byte == nullptr)
            continue;
          byte->isTainted = flag;
        }

        return flag;
      }


      bool TaintEngine::taintAssignment(const triton::arch::Register& regDst, const triton::arch::Immediate& imm) {
        return this->assignmentRegisterImmediate(regDst);
      }


      bool TaintEngine::taintAssignment(const triton::arch::Register& regDst, const triton::arch::MemoryAccess& memSrc) {
        return this->assignmentRegisterMemory(regDst, memSrc);
      }


      bool TaintEngine::taintAssignment(const triton::arch::Register& regDst, const triton::arch::Register& regSrc) {
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

        /* Spread the taint through pointers if the mode is enabled */
        if (this->modes->isModeEnabled(triton::modes::TAINT_THROUGH_POINTERS)) {
          if (this->isMemoryTainted(memSrc)) {
            this->taintMemory(memDst);
            isTainted = TAINTED;
          }
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
        bool isTainted           = !TAINTED;
        triton::uint32 writeSize = memDst.getSize();
        triton::uint64 addrDst   = memDst.getAddress();
        triton::uint64 addrSrc   = memSrc.getAddress();

        if (!this->isEnabled())
          return this->isMemoryTainted(memDst);

        /* Check source */
        for (triton::uint32 offset = 0; offset < writeSize; offset++) {
          if (this->isMemoryTainted(addrSrc+offset)) {
            this->taintMemory(addrDst+offset);
            isTainted = TAINTED;
          }
        }

        /* Spread the taint through pointers if the mode is enabled */
        if (this->modes->isModeEnabled(triton::modes::TAINT_THROUGH_POINTERS)) {
          if (this->isMemoryTainted(memSrc)) {
            this->taintMemory(memDst);
            isTainted = TAINTED;
          }
        }

        /* Check destination */
        if (this->isMemoryTainted(memDst, false)) {
          return TAINTED;
        }

        return isTainted;
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

        if (this->isMemoryTainted(memDst), false) {
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

        if (this->isMemoryTainted(memDst), false) {
          return TAINTED;
        }

        return !TAINTED;
      }

    }; /* taint namespace */
  }; /* engines namespace */
}; /* triton namespace */
