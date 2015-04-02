
#include <list>
#include <python2.7/Python.h>

#include "pin.H"


/* NameSapce for all Python Bindings variables */
namespace PyTritonOptions {
  char *startAnalysisFromName = NULL;
  bool dumpStats = false;
  bool dumpTrace = false;
  std::list<uint64_t> startAnalysisFromAddr;
  std::list<uint64_t> endAnalysisFromAddr;
};


static char Triton_runProgram_doc[] = "Start the Pin instrumentation";
static PyObject* Triton_runProgram(PyObject* self, PyObject* noarg)
{
  // Never returns - Rock 'n roll baby \o/
  PIN_StartProgram();
  return Py_None;
}

static char Triton_startAnalysisFromName_doc[] = "Start the symbolic execution from a specific";
static PyObject* Triton_startAnalysisFromName(PyObject* self, PyObject* name)
{

  if (!PyString_Check(name)){
    PyErr_Format(PyExc_TypeError, "startAnalysisFromName(): expected a string");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::startAnalysisFromName = PyString_AsString(name);
  return Py_None;
}


static char Triton_dumpTrace_doc[] = "Dump the trace at the end of the execution";
static PyObject* Triton_dumpTrace(PyObject* self, PyObject* flag)
{
  if (!PyBool_Check(flag)){
    PyErr_Format(PyExc_TypeError, "dumpTrace(): expected a boolean");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::dumpTrace = (flag == Py_True);
  return Py_None;
}


static char Triton_dumpStats_doc[] = "Dump statistics at the end of the execution";
static PyObject* Triton_dumpStats(PyObject* self, PyObject* flag)
{
  if (!PyBool_Check(flag)){
    PyErr_Format(PyExc_TypeError, "dumpStats(): expected a boolean");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::dumpStats = (flag == Py_True);
  return Py_None;
}


PyMethodDef pythonCallbacks[] = {
  {"runProgram",            Triton_runProgram,            METH_NOARGS,  Triton_runProgram_doc},
  {"startAnalysisFromName", Triton_startAnalysisFromName, METH_O,       Triton_startAnalysisFromName_doc},
  {"dumpTrace",             Triton_dumpTrace,             METH_O,       Triton_dumpTrace_doc},
  {"dumpStats",             Triton_dumpStats,             METH_O,       Triton_dumpStats_doc},
  {NULL,                    NULL,                         0,            NULL}
};

