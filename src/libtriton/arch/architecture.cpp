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
      this->arch = triton::arch::ARCH_INVALID;
      this->cpu  = nullptr;
    }


    Architecture::~Architecture() {
    }


    triton::uint32 Architecture::getArchitecture(void) const {
      return this->arch;
    }


    triton::arch::cpuInterface* Architecture::getCpu(void) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getCpu(): CPU undefined.");
      return this->cpu;
    }


    void Architecture::setArchitecture(triton::uint32 arch) {
      /* Check if the architecture is valid */
      if (!(arch > triton::arch::ARCH_INVALID && arch < triton::arch::ARCH_LAST_ITEM))
        throw std::runtime_error("Architecture::setArchitecture(): Invalid architecture.");

      /* Setup global variables */
      this->arch = arch;

      /* Allocate and init the good arch */
      switch (this->arch) {
        case triton::arch::ARCH_X86_64:
          #if defined(__i386) || defined(_M_IX86)
            throw std::runtime_error("Architecture::setArchitecture(): You cannot analyze 64-bits code on a 32-bits machine.");
          #endif
          /* remove previous CPU instance (when setArchitecture() has been called twice) */
          delete this->cpu;
          /* init the new instance */
          this->cpu = new triton::arch::x86::x8664Cpu();
          if (!this->cpu)
            throw std::runtime_error("Architecture::setArchitecture(): Not enough memory.");
          this->cpu->init();
          break;

        case triton::arch::ARCH_X86:
          /* remove previous CPU instance (when setArchitecture() has been called twice) */
          delete this->cpu;
          /* init the new instance */
          this->cpu = new triton::arch::x86::x86Cpu();
          if (!this->cpu)
            throw std::runtime_error("Architecture::setArchitecture(): Not enough memory.");
          this->cpu->init();
          break;
      }
    }


    void Architecture::clearArchitecture(void) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::clearArchitecture(): You must define an architecture.");
      this->cpu->clear();
    }


    bool Architecture::isValid(void) const {
      if (this->arch == triton::arch::ARCH_INVALID)
        return false;
      return true;
    }


    bool Architecture::isFlag(triton::uint32 regId) const {
      if (!this->cpu)
        return false;
      return this->cpu->isFlag(regId);
    }


    bool Architecture::isRegister(triton::uint32 regId) const {
      if (!this->cpu)
        return false;
      return this->cpu->isRegister(regId);
    }


    bool Architecture::isRegisterValid(triton::uint32 regId) const {
      if (!this->cpu)
        return false;
      return this->cpu->isRegisterValid(regId);
    }


    triton::uint32 Architecture::invalidRegister(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->invalidRegister();
    }


    triton::uint32 Architecture::numberOfRegisters(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->numberOfRegisters();
    }


    triton::uint32 Architecture::registerSize(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->registerSize();
    }


    triton::uint32 Architecture::registerBitSize(void) const {
      if (!this->cpu)
        return 0;
      return this->cpu->registerBitSize();
    }


    std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> Architecture::getRegisterInformation(triton::uint32 reg) const {
      std::tuple<std::string, triton::uint32, triton::uint32, triton::uint32> ret;

      std::get<0>(ret) = "unknown"; /* name           */
      std::get<1>(ret) = 0;         /* highest bit    */
      std::get<2>(ret) = 0;         /* lower bit      */
      std::get<3>(ret) = 0;         /* higest reg id  */

      if (this->cpu)
        ret = this->cpu->getRegisterInformation(reg);

      return ret;
    }


    std::set<triton::arch::RegisterOperand*> Architecture::getAllRegisters(void) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getAllRegisters(): You must define an architecture.");
      return this->cpu->getAllRegisters();
    }


    std::set<triton::arch::RegisterOperand*> Architecture::getParentRegisters(void) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getParentRegisters(): You must define an architecture.");
      return this->cpu->getParentRegisters();
    }


    void Architecture::disassembly(triton::arch::Instruction &inst) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::disassembly(): You must define an architecture.");
      this->cpu->disassembly(inst);
    }


    void Architecture::buildSemantics(triton::arch::Instruction &inst) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::buildSemantics(): You must define an architecture.");

      /* Pre IR processing */
      inst.preIRInit();

      /* If the symbolic and taint engine are disable we skip the processing */
      if (!triton::api.isSymbolicEngineEnabled() && !triton::api.isTaintEngineEnabled())
        return;

      /* Backup the symbolic engine in the case where only taint is available. */
      if (!triton::api.isSymbolicEngineEnabled())
        triton::api.backupSymbolicEngine();

      /* Processing */
      this->cpu->buildSemantics(inst);

      /* Post IR processing */
      inst.postIRInit();

      /*
       * If the symbolic engine is disable we delete symbolic
       * expressions and AST nodes. Note that if the taint engine
       * is enable we must compute semanitcs to spread the taint.
       */
      if (!triton::api.isSymbolicEngineEnabled()) {
        std::set<triton::ast::AbstractNode*> uniqueNodes;
        std::vector<triton::engines::symbolic::SymbolicExpression*>::iterator it;
        for (it = inst.symbolicExpressions.begin(); it != inst.symbolicExpressions.end(); it++) {
          triton::api.extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
          triton::api.removeSymbolicExpression((*it)->getId());
        }

        if (!triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_DICTIONARIES)) {
          /* Remove node only if AST_DICTIONARIES is disabled */
          triton::api.freeAstNodes(uniqueNodes);
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
        std::set<triton::ast::AbstractNode*> uniqueNodes;
        std::vector<triton::engines::symbolic::SymbolicExpression*> newVector;
        std::vector<triton::engines::symbolic::SymbolicExpression*>::iterator it;
        for (it = inst.symbolicExpressions.begin(); it != inst.symbolicExpressions.end(); it++) {
          if ((*it)->isTainted == triton::engines::taint::UNTAINTED) {
            triton::api.extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
            triton::api.removeSymbolicExpression((*it)->getId());
          }
          else
            newVector.push_back(*it);
        }

        if (!triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_DICTIONARIES)) {
          /* Remove node only if AST_DICTIONARIES is disabled */
          triton::api.freeAstNodes(uniqueNodes);
        }

        inst.symbolicExpressions = newVector;
      }

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on symbolized expressions, we delete all
       * concrete expressions and their AST nodes.
       */
      if (triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::ONLY_ON_SYMBOLIZED)) {
        std::set<triton::ast::AbstractNode*> uniqueNodes;
        std::vector<triton::engines::symbolic::SymbolicExpression*> newVector;
        std::vector<triton::engines::symbolic::SymbolicExpression*>::iterator it;
        for (it = inst.symbolicExpressions.begin(); it != inst.symbolicExpressions.end(); it++) {
          if ((*it)->getAst()->isSymbolized() == false) {
            triton::api.extractUniqueAstNodes(uniqueNodes, (*it)->getAst());
            triton::api.removeSymbolicExpression((*it)->getId());
          }
          else
            newVector.push_back(*it);
        }

        if (!triton::api.isSymbolicOptimizationEnabled(triton::engines::symbolic::AST_DICTIONARIES)) {
          /* Remove node only if AST_DICTIONARIES is disabled */
          triton::api.freeAstNodes(uniqueNodes);
        }

        inst.symbolicExpressions = newVector;
      }

    }


    triton::uint8 Architecture::getLastMemoryValue(triton::__uint addr) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastMemoryValue(): You must define an architecture.");
      return this->cpu->getLastMemoryValue(addr);
    }


    triton::uint512 Architecture::getLastMemoryValue(const triton::arch::MemoryOperand& mem) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastMemoryValue(): You must define an architecture.");
      return this->cpu->getLastMemoryValue(mem);
    }


    std::vector<triton::uint8> Architecture::getLastMemoryAreaValue(triton::__uint baseAddr, triton::uint32 size) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastMemoryAreaValue(): You must define an architecture.");
      return this->cpu->getLastMemoryAreaValue(baseAddr, size);
    }


    triton::uint512 Architecture::getLastRegisterValue(const triton::arch::RegisterOperand& reg) const {
      if (!this->cpu)
        throw std::runtime_error("Architecture::getLastRegisterValue(): You must define an architecture.");
      return this->cpu->getLastRegisterValue(reg);
    }


    void Architecture::setLastMemoryValue(triton::__uint addr, triton::uint8 value) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastMemoryValue(): You must define an architecture.");
      this->cpu->setLastMemoryValue(addr, value);
    }


    void Architecture::setLastMemoryValue(const triton::arch::MemoryOperand& mem) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastMemoryValue(): You must define an architecture.");
      this->cpu->setLastMemoryValue(mem);
    }


    void Architecture::setLastMemoryAreaValue(triton::__uint baseAddr, const std::vector<triton::uint8>& values) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastMemoryAreaValue(): You must define an architecture.");
      this->cpu->setLastMemoryAreaValue(baseAddr, values);
    }


    void Architecture::setLastRegisterValue(const triton::arch::RegisterOperand& reg) {
      if (!this->cpu)
        throw std::runtime_error("Architecture::setLastRegisterValue(): You must define an architecture.");
      this->cpu->setLastRegisterValue(reg);
    }

  }; /* arch namespace */
}; /* triton namespace */

