//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <new>

#include <exceptions.hpp>
#include <irBuilder.hpp>
#include <memoryAccess.hpp>
#include <operandWrapper.hpp>
#include <register.hpp>
#include <x86Semantics.hpp>



namespace triton {
  namespace arch {

    IrBuilder::IrBuilder(triton::arch::Architecture* architecture,
                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                         triton::engines::taint::TaintEngine* taintEngine) {

      if (architecture == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The architecture API must be defined.");

      if (symbolicEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The symbolic engine API must be defined.");

      if (taintEngine == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): The taint engines API must be defined.");

      this->architecture    = architecture;
      this->symbolicEngine  = symbolicEngine;
      this->taintEngine     = taintEngine;
      this->x86Isa          = new(std::nothrow) triton::arch::x86::x86Semantics(architecture, symbolicEngine, taintEngine);

      if (this->x86Isa == nullptr)
        throw triton::exceptions::IrBuilder("IrBuilder::IrBuilder(): Not enough memory.");
    }


    IrBuilder::~IrBuilder() {
      delete this->x86Isa;
    }


    bool IrBuilder::buildSemantics(triton::arch::Instruction& inst) {
      bool ret = false;

      if (this->architecture->getArchitecture() == triton::arch::ARCH_INVALID)
        throw triton::exceptions::IrBuilder("IrBuilder::buildSemantics(): You must define an architecture.");

      /* Stage 1 - Update the context memory */
      std::list<triton::arch::MemoryAccess>::iterator it1;
      for (it1 = inst.memoryAccess.begin(); it1 != inst.memoryAccess.end(); it1++) {
        this->architecture->setConcreteMemoryValue(*it1);
      }

      /* Stage 2 - Update the context register */
      std::map<triton::uint32, triton::arch::Register>::iterator it2;
      for (it2 = inst.registerState.begin(); it2 != inst.registerState.end(); it2++) {
        this->architecture->setConcreteRegisterValue(it2->second);
      }

      /* Stage 3 - Initialize the target address of memory operands */
      std::vector<triton::arch::OperandWrapper>::iterator it3;
      for (it3 = inst.operands.begin(); it3 != inst.operands.end(); it3++) {
        if (it3->getType() == triton::arch::OP_MEM) {
          it3->getMemory().initAddress();
        }
      }

      /* Pre IR processing */
      inst.preIRInit();

      /* Processing */
      switch (this->architecture->getArchitecture()) {
        case triton::arch::ARCH_X86:
        case triton::arch::ARCH_X86_64:
          ret = this->x86Isa->buildSemantics(inst);
      }

      /* Post IR processing */
      inst.postIRInit();

      return ret;
    }

  }; /* arch namespace */
}; /* triton namespace */
