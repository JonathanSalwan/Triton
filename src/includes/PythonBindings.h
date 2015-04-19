#ifndef   __PYTHONBINDINGS_H__
#define   __PYTHONBINDINGS_H__

#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>

#include "CallbackDefine.h"

extern PyMethodDef pythonCallbacks[];


namespace PyTritonOptions {

  /* Debug configurations */
  extern bool dumpStats;
  extern std::stringstream saveTrace;

  /* Execution configurations */
  extern char *startAnalysisFromSymbol;
  extern std::set<uint64_t> startAnalysisFromAddr;
  extern std::set<uint64_t> stopAnalysisFromAddr;

  /* Callback configurations */
  extern PyObject *callbackBefore; // Before the instruction processing
  extern PyObject *callbackAfter;  // After the instruction processing
  extern PyObject *callbackFini;   // At the end of the execution

  /* Taint configurations */
  extern std::map<uint64_t, std::list<uint64_t>> taintRegFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> untaintRegFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> taintMemFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> untaintMemFromAddr;
};

PyObject *initBindings(void);

/* Returns false if the script file failed to be executed. */
bool execBindings(const char *fileName);

#endif     /* !__PYTHONBINDINGS_H__ */

