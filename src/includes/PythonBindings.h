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
  extern std::set<reg_size> startAnalysisFromAddr;
  extern std::set<reg_size> startAnalysisFromOffset;
  extern std::set<reg_size> stopAnalysisFromAddr;
  extern std::set<reg_size> stopAnalysisFromOffset;

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

  /* Taint configurations */
  extern std::map<reg_size, std::list<reg_size>> taintRegFromAddr;
  extern std::map<reg_size, std::list<reg_size>> untaintRegFromAddr;
  extern std::map<reg_size, std::list<reg_size>> taintMemFromAddr;
  extern std::map<reg_size, std::list<reg_size>> untaintMemFromAddr;
};

void initBindings(void);

/* Returns false if the script file failed to be executed. */
bool execBindings(const char *fileName);

#endif     /* !__PYTHONBINDINGS_H__ */

