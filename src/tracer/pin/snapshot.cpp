//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/api.hpp>

#include <iostream>
#include "api.hpp"
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
        this->snapshotSymEngine = new triton::engines::symbolic::SymbolicEngine(*tracer::pintool::api.getSymbolicEngine());

        /* 3 - Save current taint engine state */
        this->snapshotTaintEngine = new triton::engines::taint::TaintEngine(*tracer::pintool::api.getTaintEngine());

        /* 4 - Save AST Context */
        this->astCtx = new triton::ast::AstContext(*tracer::pintool::api.getAstContext());

        /* 5 - Save the Triton CPU state */
        #if defined(__x86_64__) || defined(_M_X64)
        this->cpu = new triton::arch::x86::x8664Cpu(*dynamic_cast<triton::arch::x86::x8664Cpu*>(tracer::pintool::api.getCpuInstance()));
        #endif
        #if defined(__i386) || defined(_M_IX86)
        this->cpu = new triton::arch::x86::x86Cpu(*dynamic_cast<triton::arch::x86::x86Cpu*>(tracer::pintool::api.getCpuInstance()));
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

        /* 2 - Restore current symbolic engine state */
        *tracer::pintool::api.getSymbolicEngine() = *this->snapshotSymEngine;

        /* 3 - Restore current taint engine state */
        *tracer::pintool::api.getTaintEngine() = *this->snapshotTaintEngine;

        /* 4 - Restore AST Context */
        *tracer::pintool::api.getAstContext() = *this->astCtx;

        /* 5 - Restore the Triton CPU state */
        #if defined(__x86_64__) || defined(_M_X64)
        *dynamic_cast<triton::arch::x86::x8664Cpu*>(tracer::pintool::api.getCpuInstance()) = *this->cpu;
        #endif
        #if defined(__i386) || defined(_M_IX86)
        *dynamic_cast<triton::arch::x86::x86Cpu*>(tracer::pintool::api.getCpuInstance()) = *this->cpu;
        #endif

        /* 6 - Restore Pin registers context */
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
