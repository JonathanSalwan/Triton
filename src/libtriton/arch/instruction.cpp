//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstring>

#include <api.hpp>
#include <exceptions.hpp>
#include <immediate.hpp>
#include <instruction.hpp>



namespace triton {
  namespace arch {

    Instruction::Instruction() {
      this->address         = 0;
      this->branch          = false;
      this->conditionTaken  = false;
      this->controlFlow     = false;
      this->prefix          = 0;
      this->size            = 0;
      this->tainted         = false;
      this->tid             = 0;
      this->type            = 0;

      std::memset(this->opcodes, 0x00, sizeof(this->opcodes));
    }


    Instruction::Instruction(const triton::uint8* opcodes, triton::uint32 opSize) : Instruction::Instruction() {
      this->setOpcodes(opcodes, opSize);
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
      this->loadAccess          = other.loadAccess;
      this->memoryAccess        = other.memoryAccess;
      this->operands            = other.operands;
      this->prefix              = other.prefix;
      this->registerState       = other.registerState;
      this->size                = other.size;
      this->storeAccess         = other.storeAccess;
      this->symbolicExpressions = other.symbolicExpressions;
      this->tainted             = other.tainted;
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


    const triton::uint8* Instruction::getOpcodes(void) const {
      return this->opcodes;
    }


    void Instruction::setOpcodes(const triton::uint8* opcodes, triton::uint32 size) {
      if (size >= sizeof(this->opcodes))
       throw triton::exceptions::Instruction("Instruction::setOpcodes(): Invalid size (too big).");
      std::memcpy(this->opcodes, opcodes, size);
      this->size = size;
    }


    triton::uint32 Instruction::getSize(void) const {
      return this->size;
    }


    triton::uint32 Instruction::getType(void) const {
      return this->type;
    }


    triton::uint32 Instruction::getPrefix(void) const {
      return this->prefix;
    }


    const std::set<std::pair<triton::arch::MemoryAccess, triton::ast::AbstractNode*>>& Instruction::getLoadAccess(void) const {
      return this->loadAccess;
    }


    const std::set<std::pair<triton::arch::MemoryAccess, triton::ast::AbstractNode*>>& Instruction::getStoreAccess(void) const {
      return this->storeAccess;
    }


    const std::set<std::pair<triton::arch::Register, triton::ast::AbstractNode*>>& Instruction::getReadRegisters(void) const {
      return this->readRegisters;
    }


    const std::set<std::pair<triton::arch::Register, triton::ast::AbstractNode*>>& Instruction::getWrittenRegisters(void) const {
      return this->writtenRegisters;
    }


    const std::set<std::pair<triton::arch::Immediate, triton::ast::AbstractNode*>>& Instruction::getReadImmediates(void) const {
      return this->readImmediates;
    }


    void Instruction::updateContext(const triton::arch::MemoryAccess& mem) {
      this->memoryAccess.push_back(mem);
    }


    /* If there is a concrete value recorded, build the appropriate Register. Otherwise, perfrom the analysis on zero. */
    triton::arch::Register Instruction::getRegisterState(triton::uint32 regId) {
      triton::arch::Register reg(regId);
      if (this->registerState.find(regId) != this->registerState.end())
        reg = this->registerState[regId];
      return reg;
    }


    void Instruction::setLoadAccess(const triton::arch::MemoryAccess& mem, triton::ast::AbstractNode* node) {
      this->loadAccess.insert(std::make_pair(mem, node));
    }


    void Instruction::setStoreAccess(const triton::arch::MemoryAccess& mem, triton::ast::AbstractNode* node) {
      this->storeAccess.insert(std::make_pair(mem, node));
    }


    void Instruction::setReadRegister(const triton::arch::Register& reg, triton::ast::AbstractNode* node) {
      this->readRegisters.insert(std::make_pair(reg, node));
    }


    void Instruction::setWrittenRegister(const triton::arch::Register& reg, triton::ast::AbstractNode* node) {
      this->writtenRegisters.insert(std::make_pair(reg, node));
    }


    void Instruction::setReadImmediate(const triton::arch::Immediate& imm, triton::ast::AbstractNode* node) {
      this->readImmediates.insert(std::make_pair(imm, node));
    }


    void Instruction::setSize(triton::uint32 size) {
      this->size = size;
    }


    void Instruction::setType(triton::uint32 type) {
      this->type = type;
    }


    void Instruction::setPrefix(triton::uint32 prefix) {
      this->prefix = prefix;
    }


    void Instruction::setDisassembly(const std::string& str) {
      this->disassembly.clear();
      this->disassembly.str(str);
    }


    void Instruction::setTaint(void) {
      std::vector<triton::engines::symbolic::SymbolicExpression*>::const_iterator it;
      for (it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
        if ((*it)->isTainted == true) {
          this->tainted = true;
          break;
        }
      }
    }


    void Instruction::updateContext(const triton::arch::Register& reg) {
      this->registerState[reg.getId()] = reg;
    }


    void Instruction::addSymbolicExpression(triton::engines::symbolic::SymbolicExpression* expr) {
      if (expr == nullptr)
        throw triton::exceptions::Instruction("Instruction::addSymbolicExpression(): Cannot add a null expression.");
      this->symbolicExpressions.push_back(expr);
    }


    void Instruction::removeSymbolicExpressions(std::set<triton::ast::AbstractNode*>& uniqueNodes) {
      for (auto it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
        triton::api.extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
        triton::api.removeSymbolicExpression((*it)->getId());
      }
      this->symbolicExpressions.clear();
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
      std::vector<triton::engines::symbolic::SymbolicExpression*>::const_iterator it;
      for (it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
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


    bool Instruction::isPrefixed(void) const {
      if (this->prefix)
        return true;
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


    void Instruction::preIRInit(void) {
      /* Clear previous expressions if exist */
      this->symbolicExpressions.clear();

      /* Backup the symbolic engine in the case where only the taint is available. */
      if (!triton::api.isSymbolicEngineEnabled())
        triton::api.backupSymbolicEngine();
    }


    void Instruction::postIRInit(void) {
      std::set<triton::ast::AbstractNode*> uniqueNodes;
      std::vector<triton::engines::symbolic::SymbolicExpression*> newVector;

      /* Clear unused data */
      this->memoryAccess.clear();
      this->registerState.clear();

      /* Set the taint */
      this->setTaint();

      /*
       * If the symbolic engine is disable we delete symbolic
       * expressions and AST nodes. Note that if the taint engine
       * is enable we must compute semanitcs to spread the taint.
       */
      if (!triton::api.isSymbolicEngineEnabled()) {
        this->removeSymbolicExpressions(uniqueNodes);
        triton::api.restoreSymbolicEngine();
      }

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on tainted instructions, we delete all
       * expressions untainted and their AST nodes.
       */
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ONLY_ON_TAINTED) && !this->isTainted()) {
        this->removeSymbolicExpressions(uniqueNodes);
      }

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on symbolized expressions, we delete all
       * concrete expressions and their AST nodes.
       */
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ONLY_ON_SYMBOLIZED)) {
        for (auto it = this->symbolicExpressions.begin(); it != this->symbolicExpressions.end(); it++) {
          if ((*it)->getAst()->isSymbolized() == false) {
            triton::api.extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
            triton::api.removeSymbolicExpression((*it)->getId());
          }
          else
            newVector.push_back(*it);
        }
        this->symbolicExpressions = newVector;
      }

      /*
       * If there is no symbolic expression, clean memory operands
       * AST and implicit/explicit semantics AST to avoid memory leak.
       */
      if (this->symbolicExpressions.size() == 0) {
        /* Memory operands */
        for (auto it = this->operands.begin(); it!= this->operands.end(); it++) {
          if (it->getType() == triton::arch::OP_MEM) {
            triton::api.extractUniqueAstNodes(uniqueNodes, it->getMemory().getLeaAst());
          }
        }

        /* Implicit and explicit semantics - MEM */
        for (auto it = this->loadAccess.begin(); it!= this->loadAccess.end(); it++)
          triton::api.extractUniqueAstNodes(uniqueNodes, std::get<1>(*it));

        /* Implicit and explicit semantics - REG */
        for (auto it = this->readRegisters.begin(); it!= this->readRegisters.end(); it++)
          triton::api.extractUniqueAstNodes(uniqueNodes, std::get<1>(*it));

        /* Implicit and explicit semantics - IMM */
        for (auto it = this->readImmediates.begin(); it!= this->readImmediates.end(); it++)
          triton::api.extractUniqueAstNodes(uniqueNodes, std::get<1>(*it));
      }

      /* Free collected nodes */
      triton::api.freeAstNodes(uniqueNodes);
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
      this->size            = 0;
      this->tainted         = false;
      this->tid             = 0;
      this->type            = 0;

      this->disassembly.clear();
      this->loadAccess.clear();
      this->operands.clear();
      this->readImmediates.clear();
      this->readRegisters.clear();
      this->storeAccess.clear();
      this->symbolicExpressions.clear();
      this->writtenRegisters.clear();

      std::memset(this->opcodes, 0x00, sizeof(this->opcodes));
    }


    std::ostream& operator<<(std::ostream& stream, const Instruction& inst) {
      stream << std::hex << inst.getAddress() << ": " << inst.getDisassembly() << std::dec;
      return stream;
    }


    std::ostream& operator<<(std::ostream& stream, const Instruction* inst) {
      stream << *inst;
      return stream;
    }

  };
};

