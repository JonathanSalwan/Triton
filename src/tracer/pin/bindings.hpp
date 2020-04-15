//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_PIN_PYTHONBINDINGS_H
#define TRITON_PIN_PYTHONBINDINGS_H

/* libTriton */
#include <triton/pythonBindings.hpp>
#include <triton/api.hpp>
#include <triton/tritonTypes.hpp>

#include <map>
#include <set>
#include <vector>

#include <pin.H>

/* pintool */
#include "snapshot.hpp"
#include "trigger.hpp"
#include "utils.hpp"


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

    //! Lock / Unlock InsertCall
    extern Trigger analysisTrigger;

    //! Snapshot engine
    extern Snapshot snapshot;

    //! Python callbacks of the pintool module.
    extern PyMethodDef pintoolCallbacks[];

    //! The python script which will be executed by Pin.
    bool execScript(const char* fileName);

    #if IS_PY3
    //! The initialization of the pintool python 3 module.
    PyObject* initpintool(void);
    #else
    //! The initialization of the pintool python 2 module.
    void initpintool(void);
    #endif

    //! The initialization of the pintool python arguments.
    void initPythonArgs(int argc, char* argv[]);

    //! The Options namespace
    namespace options {
    /*!
     *  \ingroup pintool
     *  \addtogroup options
     *  @{
     */

      //! Kind of callback.
      enum cb_kind {
        CB_AFTER,           //!< After the instruction processing.
        CB_BEFORE,          //!< Before the instruction processing.
        CB_BEFORE_SYMPROC,  //!< Before the IR processing.
        CB_FINI,            //!< At the end of the execution.
        CB_ROUTINE_ENTRY,   //!< Before the routine processing.
        CB_ROUTINE_EXIT,    //!< After the routine processing.
        CB_SIGNALS,         //!< When a signal occurs.
        CB_SYSCALL_ENTRY,   //!< Before the syscall processing.
        CB_SYSCALL_EXIT,    //!< After the syscall processing.
        CB_IMAGE_LOAD,      //!< When an image is loaded.
      };

      //! Start analysis from a symbol.
      extern char* startAnalysisFromSymbol;

      //! Start analysis from the entry point.
      extern bool startAnalysisFromEntry;

      //! Start analysis from a symbol.
      extern std::set<triton::__uint> startAnalysisFromAddress;

      //! Start analysis from an offset.
      extern std::set<triton::__uint> startAnalysisFromOffset;

      //! Stop analysis from address.
      extern std::set<triton::__uint> stopAnalysisFromAddress;

      //! Stop analysis from an offset.
      extern std::set<triton::__uint> stopAnalysisFromOffset;

      //! Callback called after the instruction processing.
      extern PyObject* callbackAfter;

      //! Callback called before the instruction processing.
      extern PyObject* callbackBefore;

      //! Callback called before the IR processing.
      extern PyObject* callbackBeforeIRProc;

      //! Callback called at the end of the execution.
      extern PyObject* callbackFini;

      //! Callback called when a signal occurs.
      extern PyObject* callbackSignals;

      //! Callback called before the syscall processing.
      extern PyObject* callbackSyscallEntry;

      //! Callback called after the syscall processing.
      extern PyObject* callbackSyscallExit;

      //! Callback called when an image is loaded.
      extern PyObject* callbackImageLoad;

      //! Callback called before routine processing.
      extern std::map<const char*, PyObject*> callbackRoutineEntry;

      //! Callback callled after routine processing.
      extern std::map<const char*, PyObject*> callbackRoutineExit;

      //! An image white list.
      extern std::vector<const char*> imageWhitelist;

      //! An image black list.
      extern std::vector<const char*> imageBlacklist;

      //! TID focused during the JIT
      extern triton::uint32 targetThreadId;

    /*! @} End of options namespace */
    };

    //! The Callbacks namespace
    namespace callbacks {
    /*!
     *  \ingroup pintool
     *  \addtogroup callback
     *  @{
     */

      //! Callback called after the instruction processing.
      void after(triton::arch::Instruction* inst);

      //! Callback called before the instruction processing.
      void before(triton::arch::Instruction* inst);

      //! Callback called before the IR processing.
      void beforeIRProc(triton::arch::Instruction* inst);

      //! Callback called at the end of the execution.
      void fini(void);

      //! Callback called before and after routine processing.
      void routine(triton::uint32 threadId, PyObject* callback);

      //! Callback called when a signal occurs.
      void signals(triton::uint32 threadId, triton::sint32 sig);

      //! Callback called before the syscall processing.
      void syscallEntry(triton::uint32 threadId, triton::uint32 std);

      //! Callback called after the syscall processing.
      void syscallExit(triton::uint32 threadId, triton::uint32 std);

      //! Callback called when an image is loaded.
      void imageLoad(std::string imagePath, triton::__uint imageBase, triton::__uint imageSize);

      //! Pre processing configuration.
      void preProcessing(triton::arch::Instruction* inst, triton::uint32 threadId);

      //! Post processing configuration.
      void postProcessing(triton::arch::Instruction* inst, triton::uint32 threadId);

    /*! @} End of callback namespace */
    };

  /*! @} End of pintool namespace */
  };
/*! @} End of tracer namespace */
};

#endif /* TRITON_PIN_PYTHONBINDINGS_H */
