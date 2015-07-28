/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   PYTHONBINDINGS_H
#define   PYTHONBINDINGS_H

#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>
#include <string>

#include "CallbackDefine.h"
#include "TritonTypes.h"

extern PyMethodDef tritonCallbacks[];
extern PyMethodDef smt2libCallbacks[];


namespace PyTritonOptions {

  /* Debug configurations */
  extern bool dumpStats;
  extern std::stringstream saveTrace;

  /* Execution configurations */
  extern char *startAnalysisFromSymbol;
  extern std::set<uint64> startAnalysisFromAddr;
  extern std::set<uint64> startAnalysisFromOffset;
  extern std::set<uint64> stopAnalysisFromAddr;
  extern std::set<uint64> stopAnalysisFromOffset;

  /* Callback configurations */
  extern PyObject *callbackAfter;                                 // After the instruction processing
  extern PyObject *callbackBefore;                                // Before the instruction processing
  extern PyObject *callbackBeforeIRProc;                          // Before the IR processing
  extern PyObject *callbackFini;                                  // At the end of the execution
  extern PyObject *callbackSignals;                               // When a signal occurs
  extern PyObject *callbackSyscallEntry;                          // Before syscall processing
  extern PyObject *callbackSyscallExit;                           // After syscall processing
  extern std::map<const char *, PyObject *> callbackRoutineEntry; // Before routine processing
  extern std::map<const char *, PyObject *> callbackRoutineExit;  // After routine processing

  /* Taint configurations */
  extern std::map<uint64, std::list<uint64>> taintRegFromAddr;
  extern std::map<uint64, std::list<uint64>> untaintRegFromAddr;
  extern std::map<uint64, std::list<uint64>> taintMemFromAddr;
  extern std::map<uint64, std::list<uint64>> untaintMemFromAddr;
};

void initBindings(void);

/* Returns false if the script file failed to be executed. */
bool execBindings(const char *fileName);

#endif     /* !__PYTHONBINDINGS_H__ */

