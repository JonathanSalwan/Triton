//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
#include <api.hpp>
#include <architecture.hpp>
#include <x8664Cpu.hpp>
#include <x86Cpu.hpp>



namespace triton {
  namespace arch {

    Architecture::Architecture() {
      this->arch = ARCH_INVALID;
      this->cpu  = nullptr;
    }


    Architecture::~Architecture() {
      delete this->cpu;
    }


    triton::uint32 Architecture::getArchitecture(void) const {
      return this->arch;
    }


    triton::arch::AbstractCpu* Architecture::getCpu(void) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getCpu(): CPU undefined");
      return this->cpu;
    }


    void Architecture::setArchitecture(triton::uint32 arch) {

      /* Check if the architecture is already definied */
      if (this->arch != ARCH_INVALID)
        throw std::runtime_error("Architecture::setArchitecture(): Architecture is already defined");

      /* Check if the architecture is valid */
      if (!(arch > ARCH_INVALID && arch < ARCH_LAST_ITEM))
        throw std::runtime_error("Architecture::setArchitecture(): Invalid architecture");

      /* Setup global variables */
      this->arch = arch;

      /* Allocate and init the good arch */
      switch (this->arch) {

        case ARCH_X86_64:
          #if defined(__i386) || defined(_M_IX86)
            throw std::runtime_error("Architecture::setArchitecture(): You cannot analyze 64-bits code on a 32-bits machine.");
          #endif
          this->cpu = new x86::x8664Cpu();
          if (!this->cpu)
            throw std::runtime_error("Architecture::setArchitecture(): Not enough memory");
          this->cpu->init();
          break;

        case ARCH_X86:
          this->cpu = new x86::x86Cpu();
          if (!this->cpu)
            throw std::runtime_error("Architecture::setArchitecture(): Not enough memory");
          this->cpu->init();
          break;

      }

    }


    void Architecture::clearArchitecture(void) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::clearArchitecture(): You must define an architecture");
      this->cpu->clear();
    }


    bool Architecture::isValid(void) {
      if (this->arch == ARCH_INVALID)
        return false;
      return true;
    }


    bool Architecture::isFlag(triton::uint32 regId) {
      if (!this->cpu)
        return false;
      return this->cpu->isFlag(regId);
    }


    bool Architecture::isReg(triton::uint32 regId) {
      if (!this->cpu)
        return false;
      return this->cpu->isReg(regId);
    }


    bool Architecture::isRegValid(triton::uint32 regId) {
      if (!this->cpu)
        return false;
      return this->cpu->isRegValid(regId);
    }


    triton::uint32 Architecture::invalidReg(void) {
      if (!this->cpu)
        return 0;
      return this->cpu->invalidReg();
    }


    triton::uint32 Architecture::numberOfReg(void) {
      if (!this->cpu)
        return 0;
      return this->cpu->numberOfReg();
    }


    triton::uint32 Architecture::regSize(void) {
      if (!this->cpu)
        return 0;
      return this->cpu->regSize();
    }


    triton::uint32 Architecture::regBitSize(void) {
      if (!this->cpu)
        return 0;
      return this->cpu->regBitSize();
    }


    std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> Architecture::getRegInfo(triton::uint32 reg) {
      std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> ret;

      std::get<0>(ret) = "unknown"; /* name           */
      std::get<1>(ret) = 0;         /* highest bit    */
      std::get<2>(ret) = 0;         /* lower bit      */
      std::get<3>(ret) = 0;         /* higest reg id  */

      if (this->cpu)
        ret = this->cpu->getRegInfo(reg);

      return ret;
    }


    std::set<triton::arch::RegisterOperand*> Architecture::getParentRegisters(void) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getParentRegisters(): You must define an architecture");
      return this->cpu->getParentRegisters();
    }


    void Architecture::disassembly(triton::arch::Instruction &inst) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::disassembly(): You must define an architecture");
      this->cpu->disassembly(inst);
    }


    void Architecture::buildSemantics(triton::arch::Instruction &inst) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::disassembly(): You must define an architecture");

      /* Clear previous expressions if exist */
      inst.symbolicExpressions.clear();

      /* If the symbolic and taint engine are disable we skip the processing */
      if (!triton::api.isSymbolicEngineEnabled() && !triton::api.isTaintEngineEnabled())
        return;

      /* Backup the symbolic engine in the case where only taint is available. */
      if (!triton::api.isSymbolicEngineEnabled())
        triton::api.backupSymbolicEngine();

      /* Processing */
      this->cpu->buildSemantics(inst);

      /* Clear unused data */
      inst.memoryAccess.clear();
      inst.registerState.clear();

      /*
       * If the symbolic engine is disable we delete symbolic
       * expressions and AST nodes. Note that if the taint engine
       * is enable we must compute semanitcs to spread the taint.
       */
      if (!triton::api.isSymbolicEngineEnabled()) {
        std::set<smt2lib::smtAstAbstractNode*> uniqueNodes;
        std::vector<triton::engines::symbolic::SymbolicExpression*>::iterator it;
        for (it = inst.symbolicExpressions.begin(); it != inst.symbolicExpressions.end(); it++) {
          smt2lib::extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
          triton::api.removeSymbolicExpression((*it)->getId());
        }

        if (!triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_SUMMARIES)) {
          /* Remove node only if AST_SUMMARIES is disabled */
          smt2lib::freeAstNodes(uniqueNodes);
        }

        inst.symbolicExpressions.clear();
        triton::api.restoreSymbolicEngine();
      }

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on tainted instructions, we delete all
       * expressions untainted and their AST nodes.
       */
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ONLY_ON_TAINTED)) {
        std::set<smt2lib::smtAstAbstractNode*> uniqueNodes;
        std::vector<triton::engines::symbolic::SymbolicExpression*> newVector;
        std::vector<triton::engines::symbolic::SymbolicExpression*>::iterator it;
        for (it = inst.symbolicExpressions.begin(); it != inst.symbolicExpressions.end(); it++) {
          if ((*it)->isTainted == triton::engines::taint::UNTAINTED) {
            smt2lib::extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
            triton::api.removeSymbolicExpression((*it)->getId());
          }
          else
            newVector.push_back(*it);
        }

        if (!triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_SUMMARIES)) {
          /* Remove node only if AST_SUMMARIES is disabled */
          smt2lib::freeAstNodes(uniqueNodes);
        }

        inst.symbolicExpressions = newVector;
      }

    }


    triton::uint8 Architecture::getLastMemoryValue(triton::__uint addr) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastMemoryValue(): You must define an architecture");
      return this->cpu->getLastMemoryValue(addr);
    }


    triton::uint128 Architecture::getLastMemoryValue(triton::arch::MemoryOperand& mem) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastMemoryValue(): You must define an architecture");
      return this->cpu->getLastMemoryValue(mem);
    }


    triton::uint128 Architecture::getLastRegisterValue(triton::arch::RegisterOperand& reg) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastRegisterValue(): You must define an architecture");
      return this->cpu->getLastRegisterValue(reg);
    }


    void Architecture::setLastMemoryValue(triton::__uint addr, triton::uint8 value) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastMemoryValue(): You must define an architecture");
      this->cpu->setLastMemoryValue(addr, value);
    }


    void Architecture::setLastMemoryValue(triton::arch::MemoryOperand& mem) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastMemoryValue(): You must define an architecture");
      this->cpu->setLastMemoryValue(mem);
    }


    void Architecture::setLastRegisterValue(triton::arch::RegisterOperand& reg) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastRegisterValue(): You must define an architecture");
      this->cpu->setLastRegisterValue(reg);
    }

  }; /* arch namespace */
}; /* triton namespace */

