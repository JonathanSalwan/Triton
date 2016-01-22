//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
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

        /* 4 - Save current taint engine state */
        this->nodesList = triton::smt2lib::allocatedNodes;

        /* 5 - Save the Triton CPU state */
        #if defined(__x86_64__) || defined(_M_X64)
        this->cpu = new triton::arch::x86::x8664Cpu(*reinterpret_cast<triton::arch::x86::x8664Cpu*>(triton::api.getCpu()));
        #endif
        #if defined(__i386) || defined(_M_IX86)
        this->cpu = new triton::arch::x86::x86Cpu(*reinterpret_cast<triton::arch::x86::x86Cpu*>(triton::api.getCpu()));
        #endif

        /* 6 - Save Pin registers context */
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

        /* 2 - Delete unused expressions */
        auto currentExpressions     = triton::api.getSymbolicExpressions();
        auto snapshotExpressions    = this->snapshotSymEngine->getSymbolicExpressions();
        triton::__uint currentSize  = currentExpressions.size();
        triton::__uint snapshotSize = snapshotExpressions.size();
        for (auto i = currentExpressions.begin(); i != currentExpressions.end(); ++i) {
          if (snapshotExpressions.find(i->first) == snapshotExpressions.end())
            delete currentExpressions[i->first];
        }

        /* 3 - Delete unused variables */
        auto currentSymbolicVars   = triton::api.getSymbolicVariables();
        auto snapshotSymbolicVars  = this->snapshotSymEngine->getSymbolicVariables();
        currentSize                = currentSymbolicVars.size();
        snapshotSize               = snapshotSymbolicVars.size();
        for (auto i = currentSymbolicVars.begin(); i != currentSymbolicVars.end(); ++i) {
          if (snapshotSymbolicVars.find(i->first) == snapshotSymbolicVars.end())
            delete currentSymbolicVars[i->first];
        }

        /* 4 - Delete unused AST nodes */
        for (auto i = triton::smt2lib::allocatedNodes.begin(); i != triton::smt2lib::allocatedNodes.end(); ++i) {
          if (this->nodesList.find(*i) == this->nodesList.end())
            delete *i;
        }

        /* 5 - Restore current symbolic engine state */
        *triton::api.getSymbolicEngine() = *this->snapshotSymEngine;

        /* 6 - Restore current taint engine state */
        *triton::api.getTaintEngine() = *this->snapshotTaintEngine;

        /* 7 - Restore current AST node state */
        triton::smt2lib::allocatedNodes = this->nodesList;

        /* 8 - Restore the Triton CPU state */
        #if defined(__x86_64__) || defined(_M_X64)
        *reinterpret_cast<triton::arch::x86::x8664Cpu*>(triton::api.getCpu()) = *this->cpu;
        #endif
        #if defined(__i386) || defined(_M_IX86)
        *reinterpret_cast<triton::arch::x86::x86Cpu*>(triton::api.getCpu()) = *this->cpu;
        #endif

        /* 9 - Restore Pin registers context */
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
