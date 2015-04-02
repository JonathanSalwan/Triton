#ifndef   __PYTHONBINDINGS_H__
#define   __PYTHONBINDINGS_H__

#include <python2.7/Python.h>

extern PyMethodDef pythonCallbacks[];

/* NameSapce for all Python Bindings variables */
namespace PyTritonOptions {
  extern char *startAnalysisFromName;
  extern bool dumpStats;
  extern bool dumpTrace;
};

#endif     /* !__PYTHONBINDINGS_H__ */
