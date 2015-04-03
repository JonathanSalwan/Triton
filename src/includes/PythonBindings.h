#ifndef   __PYTHONBINDINGS_H__
#define   __PYTHONBINDINGS_H__

#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>

extern PyMethodDef pythonCallbacks[];

namespace PyTritonOptions {
  extern char *startAnalysisFromSymbol;
  extern bool dumpStats;
  extern bool dumpTrace;
  extern std::set<uint64_t> startAnalysisFromAddr;
  extern std::set<uint64_t> stopAnalysisFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> taintRegFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> untaintRegFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> taintMemFromAddr;
  extern std::map<uint64_t, std::list<uint64_t>> untaintMemFromAddr;
};

PyObject *initBindings(void);
void execBindings(const char *fileName);

#endif     /* !__PYTHONBINDINGS_H__ */

