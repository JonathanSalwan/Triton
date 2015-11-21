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
#include "PythonUtils.h"
#include "TritonTypes.h"

extern PyMethodDef tritonCallbacks[];
extern PyMethodDef smt2libCallbacks[];


namespace PyTritonOptions {

  /* Debug configurations */
  extern bool dumpStats;
  extern std::stringstream saveTrace;

  /* Execution configurations */
  extern char *startAnalysisFromSymbol;
  extern std::set<__uint> startAnalysisFromAddr;
  extern std::set<__uint> startAnalysisFromOffset;
  extern std::set<__uint> stopAnalysisFromAddr;
  extern std::set<__uint> stopAnalysisFromOffset;

  /* Callback configurations */
  extern PyObject *callbackAfter;                                 // After the instruction processing
  extern PyObject *callbackBefore;                                // Before the instruction processing
  extern PyObject *callbackBeforeIRProc;                          // Before the IR processing
  extern PyObject *callbackFini;                                  // At the end of the execution
  extern PyObject *callbackSignals;                               // When a signal occurs
  extern PyObject *callbackSyscallEntry;                          // Before syscall processing
  extern PyObject *callbackSyscallExit;                           // After syscall processing
  extern PyObject *callbackImageLoad;                             // When an image is loaded
  extern std::map<const char *, PyObject *> callbackRoutineEntry; // Before routine processing
  extern std::map<const char *, PyObject *> callbackRoutineExit;  // After routine processing
  extern std::list<const char *>            imageWhitelist;       // An image white list
  extern std::list<const char *>            imageBlacklist;       // An image black list

  /* Taint configurations */
  extern std::map<__uint, std::list<__uint>> taintRegFromAddr;
  extern std::map<__uint, std::list<__uint>> untaintRegFromAddr;
  extern std::map<__uint, std::list<__uint>> taintMemFromAddr;
  extern std::map<__uint, std::list<__uint>> untaintMemFromAddr;
};

void initBindings(void);

/* Returns false if the script file failed to be executed. */
bool execBindings(const char *fileName);

#endif     /* !__PYTHONBINDINGS_H__ */

