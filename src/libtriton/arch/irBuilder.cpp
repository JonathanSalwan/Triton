//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <new>

#include <triton/aarch64Semantics.hpp>
#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>
#include <triton/irBuilder.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/operandWrapper.hpp>
#include <triton/register.hpp>
#include <triton/x86Semantics.hpp>



namespace triton {
  namespace arch {

    IrBuilder::IrBuilder(triton::arch::Architecture* architecture,
                         triton::modes::Modes& modes,
                         triton::ast::AstContext& astCtxt,
                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                         triton::engines::taint::TaintEngine* taintEngine)
      : modes(modes) {

      if (architecture == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The architecture API must be defined.");

      if (symbolicEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The symbolic engine API must be defined.");

      if (taintEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The taint engines API must be defined.");

      this->architecture              = architecture;
      this->backupSymbolicEngine      = new(std::nothrow) triton::engines::symbolic::SymbolicEngine(architecture, modes, astCtxt, nullptr);
      this->symbolicEngine            = symbolicEngine;
      this->taintEngine               = taintEngine;
      this->aarch64Isa                = new(std::nothrow) triton::arch::aarch64::AArch64Semantics(architecture, symbolicEngine, taintEngine, astCtxt);
      this->x86Isa                    = new(std::nothrow) triton::arch::x86::x86Semantics(architecture, symbolicEngine, taintEngine, modes, astCtxt);

      if (this->x86Isa == nullptr || this->aarch64Isa == nullptr || this->backupSymbolicEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): Not enough memory.");
    }


    IrBuilder::~IrBuilder() {
      delete this->backupSymbolicEngine;
      delete this->aarch64Isa;
      delete this->x86Isa;
    }


    bool IrBuilder::buildSemantics(triton::arch::Instruction& inst) {
      bool ret = false;

      if (this->architecture->getArchitecture() == triton::arch::ARCH_INVALID)
        throw triton::exceptions::IrBuilder("IrBuilder::buildSemantics(): You must define an architecture.");

      /* Initialize the target address of memory operands */
      for (auto& operand : inst.operands) {
        if (operand.getType() == triton::arch::OP_MEM) {
          this->symbolicEngine->initLeaAst(operand.getMemory());
        }
      }

      /* Pre IR processing */
      this->preIrInit(inst);

      /* Processing */
      switch (this->architecture->getArchitecture()) {
        case triton::arch::ARCH_AARCH64:
          ret = this->aarch64Isa->buildSemantics(inst);
          break;

        case triton::arch::ARCH_X86:
        case triton::arch::ARCH_X86_64:
          ret = this->x86Isa->buildSemantics(inst);
          break;

        default:
          throw triton::exceptions::IrBuilder("IrBuilder::buildSemantics(): Architecture not supported.");
          break;
      }

      /* Post IR processing */
      this->postIrInit(inst);

      return ret;
    }


    void IrBuilder::preIrInit(triton::arch::Instruction& inst) {
      /* Clear previous expressions if exist */
      inst.symbolicExpressions.clear();

      /* Clear implicit and explicit semantics */
      inst.getLoadAccess().clear();
      inst.getReadRegisters().clear();
      inst.getReadImmediates().clear();
      inst.getStoreAccess().clear();
      inst.getWrittenRegisters().clear();

      /* Update instruction address if undefined */
      if (!inst.getAddress())
        inst.setAddress(this->architecture->getConcreteRegisterValue(this->architecture->getProgramCounter()).convert_to<triton::uint64>());

      /* Backup the symbolic engine in the case where only the taint is available. */
      if (!this->symbolicEngine->isEnabled()) {
        *this->backupSymbolicEngine = *this->symbolicEngine;
      }
    }


    void IrBuilder::postIrInit(triton::arch::Instruction& inst) {
      std::vector<triton::engines::symbolic::SharedSymbolicExpression> newVector;

      auto& loadAccess        = inst.getLoadAccess();
      auto& readRegisters     = inst.getReadRegisters();
      auto& readImmediates    = inst.getReadImmediates();
      auto& storeAccess       = inst.getStoreAccess();
      auto& writtenRegisters  = inst.getWrittenRegisters();

      /* Set the taint */
      inst.setTaint();

      // ----------------------------------------------------------------------

      /*
       * If the symbolic engine is disable we delete symbolic
       * expressions and AST nodes. Note that if the taint engine
       * is enable we must compute semanitcs to spread the taint.
       */
      if (!this->symbolicEngine->isEnabled()) {
        /* Clear memory operands */
        this->collectNodes(inst.operands);

        /* Clear implicit and explicit semantics */
        loadAccess.clear();
        readRegisters.clear();
        readImmediates.clear();
        storeAccess.clear();
        writtenRegisters.clear();

        /* Symbolic Expressions */
        this->removeSymbolicExpressions(inst);

        /* Restore backup */
        *this->symbolicEngine = *this->backupSymbolicEngine;
      }

      // ----------------------------------------------------------------------

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on symbolized expressions, we delete all
       * concrete expressions and their AST nodes.
       */
      if (this->symbolicEngine->isEnabled() && this->modes.isModeEnabled(triton::modes::ONLY_ON_SYMBOLIZED)) {
        /* Clear memory operands */
        this->collectUnsymbolizedNodes(inst.operands);

        /* Clear implicit and explicit semantics - MEM */
        this->collectUnsymbolizedNodes(loadAccess);

        /* Clear implicit and explicit semantics - REG */
        this->collectUnsymbolizedNodes(readRegisters);

        /* Clear implicit and explicit semantics - IMM */
        this->collectUnsymbolizedNodes(readImmediates);

        /* Clear implicit and explicit semantics - MEM */
        this->collectUnsymbolizedNodes(storeAccess);

        /* Clear implicit and explicit semantics - REG */
        this->collectUnsymbolizedNodes(writtenRegisters);

        /* Clear symbolic expressions */
        for (const auto& se : inst.symbolicExpressions) {
          if (se->isSymbolized() == false) {
            this->symbolicEngine->removeSymbolicExpression(se->getId());
          }
          else
            newVector.push_back(se);
        }
        inst.symbolicExpressions = newVector;
      }

      // ----------------------------------------------------------------------

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on tainted instructions, we delete all
       * expressions untainted and their AST nodes.
       */
      else if (this->modes.isModeEnabled(triton::modes::ONLY_ON_TAINTED) && !inst.isTainted()) {
        /* Memory operands */
        this->collectNodes(inst.operands);

        /* Implicit and explicit semantics - MEM */
        this->collectNodes(loadAccess);

        /* Implicit and explicit semantics - REG */
        this->collectNodes(readRegisters);

        /* Implicit and explicit semantics - IMM */
        this->collectNodes(readImmediates);

        /* Implicit and explicit semantics - MEM */
        this->collectNodes(storeAccess);

        /* Implicit and explicit semantics - REG */
        this->collectNodes(writtenRegisters);

        /* Symbolic Expressions */
        this->removeSymbolicExpressions(inst);
      }
    }


    void IrBuilder::removeSymbolicExpressions(triton::arch::Instruction& inst) {
      for (const auto& se : inst.symbolicExpressions) {
        this->symbolicEngine->removeSymbolicExpression(se->getId());
      }
      inst.symbolicExpressions.clear();
    }


    template <typename T>
    void IrBuilder::collectNodes(T& items) const {
      items.clear();
    }


    void IrBuilder::collectNodes(std::vector<triton::arch::OperandWrapper>& operands) const {
      for (auto& operand : operands) {
        if (operand.getType() == triton::arch::OP_MEM) {
          operand.getMemory().setLeaAst(nullptr);
        }
      }
    }


    template <typename T>
    void IrBuilder::collectUnsymbolizedNodes(T& items) const {
      T newItems;

      for (const auto& item : items) {
        if (std::get<1>(item) && std::get<1>(item)->isSymbolized() == true)
          newItems.insert(item);
      }

      items.clear();
      items = newItems;
    }


    void IrBuilder::collectUnsymbolizedNodes(std::vector<triton::arch::OperandWrapper>& operands) const {
      for (auto& operand : operands) {
        if (operand.getType() == triton::arch::OP_MEM) {
          if (operand.getMemory().getLeaAst() && operand.getMemory().getLeaAst()->isSymbolized() == false) {
            operand.getMemory().setLeaAst(nullptr);
          }
        }
      }
    }

  }; /* arch namespace */
}; /* triton namespace */
