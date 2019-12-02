//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <triton/exceptions.hpp>
#include <triton/immediate.hpp>
#include <triton/instruction.hpp>



namespace triton {
  namespace arch {

    Instruction::Instruction() {
      this->address         = 0;
      this->branch          = false;
      this->codeCondition   = triton::arch::arm::ID_CONDITION_INVALID;
      this->conditionTaken  = 0;
      this->controlFlow     = false;
      this->prefix          = triton::arch::x86::ID_PREFIX_INVALID;
      this->size            = 0;
      this->tainted         = false;
      this->thumb           = false;
      this->tid             = 0;
      this->type            = 0;
      this->updateFlag      = false;
      this->writeBack       = false;

      std::memset(this->opcode, 0x00, sizeof(this->opcode));
    }


    Instruction::Instruction(const triton::uint8* opcode, triton::uint32 opSize) : Instruction::Instruction() {
      this->setOpcode(opcode, opSize);
    }


    Instruction::Instruction(const Instruction& other) {
      this->copy(other);
    }


    Instruction::~Instruction() {
      /* See #828: Release ownership before calling container destructor */
      this->loadAccess.clear();
      this->readImmediates.clear();
      this->readRegisters.clear();
      this->storeAccess.clear();
      this->symbolicExpressions.clear();
      this->writtenRegisters.clear();
    }


    Instruction& Instruction::operator=(const Instruction& other) {
      this->copy(other);
      return *this;
    }


    void Instruction::copy(const Instruction& other) {
      this->address             = other.address;
      this->branch              = other.branch;
      this->codeCondition       = other.codeCondition;
      this->conditionTaken      = other.conditionTaken;
      this->controlFlow         = other.controlFlow;
      this->loadAccess          = other.loadAccess;
      this->operands            = other.operands;
      this->prefix              = other.prefix;
      this->readImmediates      = other.readImmediates;
      this->readRegisters       = other.readRegisters;
      this->size                = other.size;
      this->storeAccess         = other.storeAccess;
      this->symbolicExpressions = other.symbolicExpressions;
      this->tainted             = other.tainted;
      this->tid                 = other.tid;
      this->type                = other.type;
      this->undefinedRegisters  = other.undefinedRegisters;
      this->updateFlag          = other.updateFlag;
      this->writeBack           = other.writeBack;
      this->writtenRegisters    = other.writtenRegisters;

      std::memcpy(this->opcode, other.opcode, sizeof(this->opcode));

      this->disassembly.clear();
      this->disassembly.str(other.disassembly.str());
    }


    triton::uint32 Instruction::getThreadId(void) const {
      return this->tid;
    }


    void Instruction::setThreadId(triton::uint32 tid) {
      this->tid = tid;
    }


    triton::uint64 Instruction::getAddress(void) const {
      return this->address;
    }


    triton::uint64 Instruction::getNextAddress(void) const {
      return this->address + this->size;
    }


    void Instruction::setAddress(triton::uint64 addr) {
      this->address = addr;
    }


    std::string Instruction::getDisassembly(void) const {
      return this->disassembly.str();
    }


    const triton::uint8* Instruction::getOpcode(void) const {
      return this->opcode;
    }


    void Instruction::setOpcode(const triton::uint8* opcode, triton::uint32 size) {
      if (size >= sizeof(this->opcode))
       throw triton::exceptions::Instruction("Instruction::setOpcode(): Invalid size (too big).");
      std::memcpy(this->opcode, opcode, size);
      this->size = size;
    }


    triton::uint32 Instruction::getSize(void) const {
      return this->size;
    }


    triton::uint32 Instruction::getType(void) const {
      return this->type;
    }


    triton::arch::x86::prefix_e Instruction::getPrefix(void) const {
      return this->prefix;
    }


    triton::arch::arm::condition_e Instruction::getCodeCondition(void) const {
      return this->codeCondition;
    }


    std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>>& Instruction::getLoadAccess(void) {
      return this->loadAccess;
    }


    std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>>& Instruction::getStoreAccess(void) {
      return this->storeAccess;
    }


    std::set<std::pair<triton::arch::Register, triton::ast::SharedAbstractNode>>& Instruction::getReadRegisters(void) {
      return this->readRegisters;
    }


    std::set<std::pair<triton::arch::Register, triton::ast::SharedAbstractNode>>& Instruction::getWrittenRegisters(void) {
      return this->writtenRegisters;
    }


    std::set<std::pair<triton::arch::Immediate, triton::ast::SharedAbstractNode>>& Instruction::getReadImmediates(void) {
      return this->readImmediates;
    }


    std::set<triton::arch::Register>& Instruction::getUndefinedRegisters(void) {
      return this->undefinedRegisters;
    }


    void Instruction::setLoadAccess(const triton::arch::MemoryAccess& mem, const triton::ast::SharedAbstractNode& node) {
      this->loadAccess.insert(std::make_pair(mem, node));
    }


    void Instruction::removeLoadAccess(const triton::arch::MemoryAccess& mem) {
      auto it = this->loadAccess.begin();

      while (it != this->loadAccess.end()) {
        if (it->first.getAddress() == mem.getAddress())
          it = this->loadAccess.erase(it);
        else
          ++it;
      }
    }


    void Instruction::setStoreAccess(const triton::arch::MemoryAccess& mem, const triton::ast::SharedAbstractNode& node) {
      this->storeAccess.insert(std::make_pair(mem, node));
    }


    void Instruction::removeStoreAccess(const triton::arch::MemoryAccess& mem) {
      auto it = this->storeAccess.begin();

      while (it != this->storeAccess.end()) {
        if (it->first.getAddress() == mem.getAddress())
          it = this->storeAccess.erase(it);
        else
          ++it;
      }
    }


    void Instruction::setReadRegister(const triton::arch::Register& reg, const triton::ast::SharedAbstractNode& node) {
      this->readRegisters.insert(std::make_pair(reg, node));
    }


    void Instruction::removeReadRegister(const triton::arch::Register& reg) {
      auto it = this->readRegisters.begin();

      while (it != this->readRegisters.end()) {
        if (it->first.getId() == reg.getId())
          it = this->readRegisters.erase(it);
        else
          ++it;
      }
    }


    void Instruction::setWrittenRegister(const triton::arch::Register& reg, const triton::ast::SharedAbstractNode& node) {
      this->writtenRegisters.insert(std::make_pair(reg, node));
    }


    void Instruction::removeWrittenRegister(const triton::arch::Register& reg) {
      auto it = this->writtenRegisters.begin();

      while (it != this->writtenRegisters.end()) {
        if (it->first.getId() == reg.getId())
          it = this->writtenRegisters.erase(it);
        else
          ++it;
      }
    }


    void Instruction::setReadImmediate(const triton::arch::Immediate& imm, const triton::ast::SharedAbstractNode& node) {
      this->readImmediates.insert(std::make_pair(imm, node));
    }


    void Instruction::removeReadImmediate(const triton::arch::Immediate& imm) {
      auto it = this->readImmediates.begin();

      while (it != this->readImmediates.end()) {
        if (it->first.getValue() == imm.getValue())
          it = this->readImmediates.erase(it);
        else
          ++it;
      }
    }


    void Instruction::setUndefinedRegister(const triton::arch::Register& reg) {
      this->undefinedRegisters.insert(reg);
    }


    void Instruction::removeUndefinedRegister(const triton::arch::Register& reg) {
      this->undefinedRegisters.erase(reg);
    }


    void Instruction::setSize(triton::uint32 size) {
      this->size = size;
    }


    void Instruction::setType(triton::uint32 type) {
      this->type = type;
    }


    void Instruction::setPrefix(triton::arch::x86::prefix_e prefix) {
      this->prefix = prefix;
    }


    void Instruction::setWriteBack(bool state) {
      this->writeBack = state;
    }


    void Instruction::setUpdateFlag(bool state) {
      this->updateFlag = state;
    }


    void Instruction::setCodeCondition(triton::arch::arm::condition_e codeCondition) {
      this->codeCondition = codeCondition;
    }


    void Instruction::setThumb(bool state) {
      this->thumb = state;
    }


    void Instruction::setDisassembly(const std::string& str) {
      this->disassembly.clear();
      this->disassembly.str(str);
    }


    void Instruction::setTaint(bool state) {
      this->tainted = state;
    }


    void Instruction::setTaint(void) {
      for (auto it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
        if ((*it)->isTainted == true) {
          this->tainted = true;
          break;
        }
      }
    }


    const triton::engines::symbolic::SharedSymbolicExpression& Instruction::addSymbolicExpression(const triton::engines::symbolic::SharedSymbolicExpression& expr) {
      if (expr == nullptr)
        throw triton::exceptions::Instruction("Instruction::addSymbolicExpression(): Cannot add a null expression.");
      this->symbolicExpressions.push_back(expr);
      return this->symbolicExpressions.back();
    }


    bool Instruction::isBranch(void) const {
      return this->branch;
    }


    bool Instruction::isControlFlow(void) const {
      return this->controlFlow;
    }


    bool Instruction::isConditionTaken(void) const {
      return this->conditionTaken;
    }


    bool Instruction::isTainted(void) const {
      return this->tainted;
    }


    bool Instruction::isSymbolized(void) const {
      for (auto it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
        if ((*it)->isSymbolized() == true)
          return true;
      }
      return false;
    }


    bool Instruction::isMemoryRead(void) const {
      if (this->loadAccess.size() >= 1)
        return true;
      return false;
    }


    bool Instruction::isMemoryWrite(void) const {
      if (this->storeAccess.size() >= 1)
        return true;
      return false;
    }


    bool Instruction::isReadFrom(const triton::arch::OperandWrapper& target) const {
      switch(target.getType()) {

        case triton::arch::OP_IMM:
          for (auto&& pair : this->readImmediates) {
            if (pair.first == target.getConstImmediate())
              return true;
          }
          break;

        case triton::arch::OP_MEM:
          for (auto&& pair : this->loadAccess) {
            const triton::arch::MemoryAccess& m1 = pair.first;
            const triton::arch::MemoryAccess& m2 = target.getConstMemory();

            if (m1.isOverlapWith(m2))
              return true;
          }
          break;

        case triton::arch::OP_REG:
          for (auto&& pair : this->readRegisters) {
            const triton::arch::Register& r1 = pair.first;
            const triton::arch::Register& r2 = target.getConstRegister();

            if (r1.isOverlapWith(r2))
              return true;
          }
          break;

        default:
          throw triton::exceptions::Instruction("Instruction::isReadFrom(): Invalid type operand.");
      }

      return false;
    }


    bool Instruction::isWriteTo(const triton::arch::OperandWrapper& target) const {
      switch(target.getType()) {

        case triton::arch::OP_IMM:
          break;

        case triton::arch::OP_MEM:
          for (auto&& pair : this->storeAccess) {
            const triton::arch::MemoryAccess& m1 = pair.first;
            const triton::arch::MemoryAccess& m2 = target.getConstMemory();

            if (m1.isOverlapWith(m2))
              return true;
          }
          break;

        case triton::arch::OP_REG:
          for (auto&& pair : this->writtenRegisters) {
            const triton::arch::Register& r1 = pair.first;
            const triton::arch::Register& r2 = target.getConstRegister();

            if (r1.isOverlapWith(r2))
              return true;
          }
          break;

        default:
          throw triton::exceptions::Instruction("Instruction::isWriteTo(): Invalid type operand.");
      }

      return false;
    }


    bool Instruction::isPrefixed(void) const {
      if (this->prefix == triton::arch::x86::ID_PREFIX_INVALID)
        return false;
      return true;
    }


    bool Instruction::isWriteBack(void) const {
      return this->writeBack;
    }


    bool Instruction::isUpdateFlag(void) const {
      return this->updateFlag;
    }


    bool Instruction::isThumb(void) const {
      return this->thumb;
    }


    void Instruction::setBranch(bool flag) {
      this->branch = flag;
    }


    void Instruction::setControlFlow(bool flag) {
      this->controlFlow = flag;
    }


    void Instruction::setConditionTaken(bool flag) {
      this->conditionTaken = flag;
    }


    void Instruction::clear(void) {
      this->address         = 0;
      this->branch          = false;
      this->codeCondition   = triton::arch::arm::ID_CONDITION_INVALID;
      this->conditionTaken  = 0;
      this->controlFlow     = false;
      this->prefix          = triton::arch::x86::ID_PREFIX_INVALID;
      this->size            = 0;
      this->tainted         = false;
      this->tid             = 0;
      this->type            = 0;
      this->updateFlag      = false;
      this->writeBack       = false;

      this->disassembly.clear();
      this->loadAccess.clear();
      this->operands.clear();
      this->readImmediates.clear();
      this->readRegisters.clear();
      this->storeAccess.clear();
      this->symbolicExpressions.clear();
      this->writtenRegisters.clear();

      std::memset(this->opcode, 0x00, sizeof(this->opcode));
    }


    std::ostream& operator<<(std::ostream& stream, const Instruction& inst) {
      stream << "0x" << std::hex << inst.getAddress() << ": " << inst.getDisassembly() << std::dec;
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const Instruction* inst) {
      stream << *inst;
      return stream;
    }

  };
};
