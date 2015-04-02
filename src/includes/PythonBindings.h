#ifndef   __PYTHONBINDINGS_H__
#define   __PYTHONBINDINGS_H__

#include <list>
#include <python2.7/Python.h>

extern PyMethodDef pythonCallbacks[];

namespace PyTritonOptions {
  extern char *startAnalysisFromName;
  extern bool dumpStats;
  extern bool dumpTrace;
  extern std::list<uint64_t> startAnalysisFromAddr;
  extern std::list<uint64_t> endAnalysisFromAddr;
};

#endif     /* !__PYTHONBINDINGS_H__ */

