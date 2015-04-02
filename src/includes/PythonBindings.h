#ifndef   __PYTHONBINDINGS_H__
#define   __PYTHONBINDINGS_H__

#include <set>
#include <python2.7/Python.h>

extern PyMethodDef pythonCallbacks[];

namespace PyTritonOptions {
  extern char *startAnalysisFromName;
  extern bool dumpStats;
  extern bool dumpTrace;
  extern std::set<uint64_t> startAnalysisFromAddr;
  extern std::set<uint64_t> stopAnalysisFromAddr;
};

#endif     /* !__PYTHONBINDINGS_H__ */

