//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <new>

#include <triton/aarch64Semantics.hpp>
#include <triton/arm32Semantics.hpp>
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
                         const triton::modes::SharedModes& modes,
                         const triton::ast::SharedAstContext& astCtxt,
                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                         triton::engines::taint::TaintEngine* taintEngine)
      : modes(modes), astCtxt(astCtxt) {

      if (architecture == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The architecture API must be defined.");

      if (symbolicEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The symbolic engine API must be defined.");

      if (taintEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The taint engines API must be defined.");

      this->architecture         = architecture;
      this->symbolicEngine       = symbolicEngine;
      this->taintEngine          = taintEngine;
      this->aarch64Isa           = new(std::nothrow) triton::arch::arm::aarch64::AArch64Semantics(architecture, symbolicEngine, taintEngine, astCtxt);
      this->arm32Isa             = new(std::nothrow) triton::arch::arm::arm32::Arm32Semantics(architecture, symbolicEngine, taintEngine, astCtxt);
      this->x86Isa               = new(std::nothrow) triton::arch::x86::x86Semantics(architecture, symbolicEngine, taintEngine, modes, astCtxt);

      if (this->x86Isa == nullptr || this->aarch64Isa == nullptr || this->arm32Isa == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): Not enough memory.");
    }


    IrBuilder::~IrBuilder() {
      delete this->aarch64Isa;
      delete this->arm32Isa;
      delete this->x86Isa;
    }


    triton::arch::exception_e IrBuilder::buildSemantics(triton::arch::Instruction& inst) {
      triton::arch::architecture_e arch = this->architecture->getArchitecture();
      triton::arch::exception_e ret = triton::arch::NO_FAULT;

      if (arch == triton::arch::ARCH_INVALID)
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
      switch (arch) {
        case triton::arch::ARCH_AARCH64:
          ret = this->aarch64Isa->buildSemantics(inst);
          break;

        case triton::arch::ARCH_ARM32:
          ret = this->arm32Isa->buildSemantics(inst);
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


    triton::arch::exception_e IrBuilder::buildSemantics(triton::arch::BasicBlock& block) {
      triton::arch::exception_e ret = triton::arch::NO_FAULT;
      triton::usize count = block.getSize();

      for (auto& inst : block.getInstructions()) {
        ret = this->buildSemantics(inst);
        if (ret != triton::arch::NO_FAULT) {
          return ret;
        }
        count--;
        if (inst.isControlFlow() && count) {
          throw triton::exceptions::IrBuilder("IrBuilder::buildSemantics(): Do not add instructions in a block after a branch instruction.");
        }
      }

      return ret;
    }


    void IrBuilder::preIrInit(triton::arch::Instruction& inst) {
      /* Clear previous expressions if exist */
      inst.symbolicExpressions.clear();

      /* Clear implicit and explicit previous semantics */
      inst.getLoadAccess().clear();
      inst.getReadRegisters().clear();
      inst.getReadImmediates().clear();
      inst.getStoreAccess().clear();
      inst.getWrittenRegisters().clear();

      /* Update instruction address if undefined */
      if (!inst.getAddress()) {
        inst.setAddress(static_cast<triton::uint64>(this->architecture->getConcreteRegisterValue(this->architecture->getProgramCounter())));
      }
    }


    void IrBuilder::postIrInit(triton::arch::Instruction& inst) {
      std::vector<triton::engines::symbolic::SharedSymbolicExpression> newVector;

      /* Set the taint */
      inst.setTaint();

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on symbolized expressions, we delete all
       * concrete expressions and their AST nodes.
       */
      if (this->modes->isModeEnabled(triton::modes::ONLY_ON_SYMBOLIZED)) {
        /* Clear memory operands */
        this->collectUnsymbolizedNodes(inst.operands);

        /* Clear implicit and explicit semantics - MEM */
        this->collectUnsymbolizedNodes(inst.getLoadAccess());

        /* Clear implicit and explicit semantics - REG */
        this->collectUnsymbolizedNodes(inst.getReadRegisters());

        /* Clear implicit and explicit semantics - IMM */
        this->collectUnsymbolizedNodes(inst.getReadImmediates());

        /* Clear implicit and explicit semantics - MEM */
        this->collectUnsymbolizedNodes(inst.getStoreAccess());

        /* Clear implicit and explicit semantics - REG */
        this->collectUnsymbolizedNodes(inst.getWrittenRegisters());

        /* Clear symbolic expressions */
        for (const auto& se : inst.symbolicExpressions) {
          if (se->isSymbolized() == false) {
            this->symbolicEngine->removeSymbolicExpression(se);
          }
          else
            newVector.push_back(se);
        }
        inst.symbolicExpressions = newVector;
      }

      /*
       * If the symbolic engine is defined to process symbolic
       * execution only on tainted instructions, we delete all
       * expressions untainted and their AST nodes.
       */
      else if (this->modes->isModeEnabled(triton::modes::ONLY_ON_TAINTED) && !inst.isTainted()) {
        /* Memory operands */
        this->collectNodes(inst.operands);

        /* Implicit and explicit semantics - MEM */
        this->collectNodes(inst.getLoadAccess());

        /* Implicit and explicit semantics - REG */
        this->collectNodes(inst.getReadRegisters());

        /* Implicit and explicit semantics - IMM */
        this->collectNodes(inst.getReadImmediates());

        /* Implicit and explicit semantics - MEM */
        this->collectNodes(inst.getStoreAccess());

        /* Implicit and explicit semantics - REG */
        this->collectNodes(inst.getWrittenRegisters());

        /* Symbolic Expressions */
        this->removeSymbolicExpressions(inst);
      }

      this->astCtxt->garbage();
    }


    void IrBuilder::removeSymbolicExpressions(triton::arch::Instruction& inst) {
      for (const auto& se : inst.symbolicExpressions) {
        this->symbolicEngine->removeSymbolicExpression(se);
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
