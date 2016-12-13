//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <iostream>
#include "snapshot.hpp"



namespace tracer {
  namespace pintool {

      Snapshot::Snapshot() {
        this->locked              = true;
        this->snapshotTaintEngine = nullptr;
        this->snapshotSymEngine   = nullptr;
        this->mustBeRestore       = false;
      }


      Snapshot::~Snapshot() {
      }


      /* Add the modification byte. */
      void Snapshot::addModification(triton::__uint mem, char byte) {
        if (this->locked == false && this->memory.find(mem) == this->memory.end())
          this->memory[mem] = byte;
      }


      /* Enable the snapshot engine. */
      void Snapshot::takeSnapshot(CONTEXT *ctx) {
        /* 1 - Unlock the engine */
        this->locked = false;

        /* 2 - Save current symbolic engine state */
        this->snapshotSymEngine = new triton::engines::symbolic::SymbolicEngine(*triton::api.getSymbolicEngine());

        /* 3 - Save current taint engine state */
        this->snapshotTaintEngine = new triton::engines::taint::TaintEngine(*triton::api.getTaintEngine());

        /* 4 - Save current set of nodes */
        this->nodesList = triton::api.getAllocatedAstNodes();

        /* 5 - Save current map of variables */
        this->variablesMap = triton::api.getAstVariableNodes();

        /* 6 - Save the Triton CPU state */
        #if defined(__x86_64__) || defined(_M_X64)
        this->cpu = new triton::arch::x86::x8664Cpu(*dynamic_cast<triton::arch::x86::x8664Cpu*>(triton::api.getCpu()));
        #endif
        #if defined(__i386) || defined(_M_IX86)
        this->cpu = new triton::arch::x86::x86Cpu(*dynamic_cast<triton::arch::x86::x86Cpu*>(triton::api.getCpu()));
        #endif

        /* 7 - Save Pin registers context */
        PIN_SaveContext(ctx, &this->pinCtx);
      }


      /* Restore the snapshot. */
      void Snapshot::restoreSnapshot(CONTEXT *ctx) {

        if (this->mustBeRestore == false)
          return;

        /* 1 - Restore all memory modification. */
        for(auto i = this->memory.begin(); i != this->memory.end(); ++i){
          *(reinterpret_cast<char*>(i->first)) = i->second;
        }
        this->memory.clear();

        /* 2 - Restore current symbolic engine state */
        *triton::api.getSymbolicEngine() = *this->snapshotSymEngine;

        /* 3 - Restore current taint engine state */
        *triton::api.getTaintEngine() = *this->snapshotTaintEngine;

        /* 4 - Restore current AST node state */
        triton::api.setAllocatedAstNodes(this->nodesList);

        /* 5 - Restore current variables map state */
        triton::api.setAstVariableNodes(this->variablesMap);

        /* 6 - Restore the Triton CPU state */
        #if defined(__x86_64__) || defined(_M_X64)
        *dynamic_cast<triton::arch::x86::x8664Cpu*>(triton::api.getCpu()) = *this->cpu;
        #endif
        #if defined(__i386) || defined(_M_IX86)
        *dynamic_cast<triton::arch::x86::x86Cpu*>(triton::api.getCpu()) = *this->cpu;
        #endif

        /* 7 - Restore Pin registers context */
        PIN_SaveContext(&this->pinCtx, ctx);

        this->mustBeRestore = false;
        PIN_UnlockClient();
        PIN_ExecuteAt(ctx);
      }


      /* Disable the snapshot engine. */
      void Snapshot::disableSnapshot(void) {
        this->locked = true;
      }


      /* Reset the snapshot engine.
       * Clear all backups for a new snapshot. */
      void Snapshot::resetEngine(void) {
        this->memory.clear();

        delete this->snapshotSymEngine;
        this->snapshotSymEngine = nullptr;

        delete this->snapshotTaintEngine;
        this->snapshotTaintEngine = nullptr;
      }


      /* Check if the snapshot engine is locked. */
      bool Snapshot::isLocked(void) {
        return this->locked;
      }


      CONTEXT *Snapshot::getCtx(void) {
        return &this->pinCtx;
      }


      /* Check if we must restore the snapshot */
      bool Snapshot::mustBeRestored(void) {
        return this->mustBeRestore;
      }


      /* Check if we must restore the snapshot */
      void Snapshot::setRestore(bool flag) {
        this->mustBeRestore = flag;
      }

  };
};
