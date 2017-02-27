//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef PINTOOL_SNAPSHOT_H
#define PINTOOL_SNAPSHOT_H

#include <map>
#include <set>

#include <pin.H>

/* libTriton */
#include <triton/api.hpp>
#include <triton/ast.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/taintEngine.hpp>
#include <triton/x8664Cpu.hpp>
#include <triton/x86Cpu.hpp>


//! The Tracer namespace
namespace tracer {
/*!
 *  \addtogroup tracer
 *  @{
 */

  //! The Pintool namespace
  namespace pintool {
  /*!
   *  \ingroup tracer
   *  \addtogroup pintool
   *  @{
   */

    //! \class Snapshot
    //! \brief the snapshot class.
    class Snapshot {

      private:
        //! I/O memory monitoring for snapshot.
        std::map<triton::__uint, char> memory;

        //! Status of the snapshot engine.
        bool locked;

        //! Flag which defines if we must restore the snapshot.
        bool mustBeRestore;

        //! AST node state.
        std::set<triton::ast::AbstractNode*> nodesList;

        //! Variables node state.
        std::map<std::string, triton::ast::AbstractNode*> variablesMap;

        //! Snapshot of the symbolic engine.
        triton::engines::symbolic::SymbolicEngine* snapshotSymEngine;

        //! Snapshot of the taint engine.
        triton::engines::taint::TaintEngine* snapshotTaintEngine;

        //! Snapshot of triton CPU.
        #if defined(__x86_64__) || defined(_M_X64)
        triton::arch::x86::x8664Cpu* cpu;
        #endif
        #if defined(__i386) || defined(_M_IX86)
        triton::arch::x86::x86Cpu* cpu;
        #endif

        //! Snapshot of Pin context.
        CONTEXT pinCtx;


      public:
        //! Constructor.
        Snapshot();

        //! Destructor.
        ~Snapshot();

        //! Returns the Pin context.
        CONTEXT *getCtx(void);

        //! Returns true if the snapshot engine is disabled.
        bool isLocked(void);

        //! Returns true if we must restore the context.
        bool mustBeRestored(void);

        //! Adds a memory modifiction.
        void addModification(triton::__uint address, char byte);

        //! Disables the snapshot engine.
        void disableSnapshot(void);

        //! Resets the snapshot engine.
        void resetEngine(void);

        //! Restores a snapshot.
        void restoreSnapshot(CONTEXT *ctx);

        //! Sets the restore flag.
        void setRestore(bool flag);

        //! Takes a snapshot.
        void takeSnapshot(CONTEXT *ctx);
    };

  /*! @} End of pintool namespace */
  };
/*! @} End of tracer namespace */
};

#endif /* PINTOOL_SNAPSHOT_H */

