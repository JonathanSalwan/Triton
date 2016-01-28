//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <cstring>

#include <api.hpp>
#include <immediateOperand.hpp>
#include <instruction.hpp>



namespace triton {
  namespace arch {

    Instruction::Instruction() {
      this->address         = 0;
      this->branch          = false;
      this->conditionTaken  = false;
      this->controlFlow     = false;
      this->opcodesSize     = 0;
      this->tid             = 0;
      this->type            = 0;
      std::memset(this->opcodes, 0x00, sizeof(this->opcodes));
    }


    Instruction::~Instruction() {
    }


    Instruction::Instruction(const Instruction& other) {
      this->copy(other);
    }


    void Instruction::operator=(const Instruction& other) {
      this->copy(other);
    }


    void Instruction::copy(const Instruction& other) {
      this->address             = other.address;
      this->branch              = other.branch;
      this->conditionTaken      = other.conditionTaken;
      this->controlFlow         = other.controlFlow;
      this->memoryAccess        = other.memoryAccess;
      this->opcodesSize         = other.opcodesSize;
      this->operands            = other.operands;
      this->registerState       = other.registerState;
      this->symbolicExpressions = other.symbolicExpressions;
      this->tid                 = other.tid;
      this->type                = other.type;

      std::memcpy(this->opcodes, other.opcodes, sizeof(this->opcodes));

      this->disassembly.clear();
      this->disassembly.str(other.disassembly.str());
    }


    triton::uint32 Instruction::getThreadId(void) const {
      return this->tid;
    }


    void Instruction::setThreadId(triton::uint32 tid) {
      this->tid = tid;
    }


    triton::__uint Instruction::getAddress(void) const {
      return this->address;
    }


    triton::__uint Instruction::getNextAddress(void) const {
      return this->address + this->opcodesSize;
    }


    void Instruction::setAddress(triton::__uint addr) {
      this->address = addr;
    }


    std::string Instruction::getDisassembly(void) const {
      return this->disassembly.str();
    }


    const triton::uint8* Instruction::getOpcodes(void) const {
      return this->opcodes;
    }


    void Instruction::setOpcodes(triton::uint8* opcodes, triton::uint32 size) {
      if (size >= sizeof(this->opcodes))
       throw std::runtime_error("Instruction::setOpcodes(): Invalid size (too big)");
      std::memcpy(this->opcodes, opcodes, size);
      this->opcodesSize = size;
    }


    triton::uint32 Instruction::getOpcodesSize(void) const {
      return this->opcodesSize;
    }


    triton::uint32 Instruction::getType(void) const {
      return this->type;
    }


    void Instruction::updateContext(triton::arch::MemoryOperand mem) {
      this->memoryAccess.push_back(mem);
    }


    triton::arch::MemoryOperand Instruction::popMemoryAccess(triton::__uint addr, triton::uint32 size, triton::uint128 value) {
      /* The default value is zero */
      triton::arch::MemoryOperand mem;

      /* If there is a default value specified, we use it */
      if (size)
        mem = triton::arch::MemoryOperand(addr, size, value);

      /* If there is a memory access recorded, we use it */
      if (this->memoryAccess.size() > 0) {
        mem = this->memoryAccess.front();
        triton::api.setLastMemoryValue(mem);
        this->memoryAccess.pop_front();
      }

      return mem;
    }


    /* If there is a concrete value recorded, build the appropriate RegisterOperand. Otherwise, perfrom the analysis on zero. */
    triton::arch::RegisterOperand Instruction::getRegisterState(triton::uint32 regId) {
      triton::arch::RegisterOperand reg(regId);
      if (this->registerState.find(regId) != this->registerState.end())
        reg = this->registerState[regId];
      return reg;
    }


    void Instruction::setType(triton::uint32 type) {
      this->type = type;
    }


    void Instruction::setDisassembly(std::string str) {
      this->disassembly.clear();
      this->disassembly.str(str);
    }


    void Instruction::updateContext(triton::arch::RegisterOperand reg) {
      if (reg.isFlag())
        throw std::runtime_error("Instruction::updateContext(): You cannot update the context on an isolated flag.");
      this->registerState[reg.getId()] = reg;
    }


    void Instruction::addSymbolicExpression(triton::engines::symbolic::SymbolicExpression* expr) {
      if (expr == nullptr)
        throw std::runtime_error("Instruction::addSymbolicExpression(): Cannot add a null expression.");
      this->symbolicExpressions.push_back(expr);
    }


    bool Instruction::isBranch(void) {
      return this->branch;
    }


    bool Instruction::isControlFlow(void) {
      return this->controlFlow;
    }


    bool Instruction::isConditionTaken(void) {
      return this->conditionTaken;
    }


    bool Instruction::isTainted(void) {
      std::vector<triton::engines::symbolic::SymbolicExpression*>::iterator it;
      for (it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
        if ((*it)->isTainted == true)
          return true;
      }
      return false;
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


    void Instruction::reset(void) {
      this->partialReset();
      this->memoryAccess.clear();
      this->registerState.clear();
    }


    void Instruction::partialReset(void) {
      this->address         = 0;
      this->branch          = false;
      this->conditionTaken  = false;
      this->controlFlow     = false;
      this->opcodesSize     = 0;
      this->tid             = 0;
      this->type            = 0;

      this->operands.clear();
      this->symbolicExpressions.clear();
      this->disassembly.clear();

      std::memset(this->opcodes, 0x00, sizeof(this->opcodes));
    }


    std::ostream &operator<<(std::ostream &stream, Instruction inst) {
      stream << std::hex << inst.getAddress() << ": " << inst.getDisassembly() << std::dec;
      return stream;
    }

  };
};

