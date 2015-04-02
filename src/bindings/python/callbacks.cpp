
#include <map>
#include <python2.7/Python.h>
#include <set>

#include "pin.H"


/* NameSapce for all Python Bindings variables */
namespace PyTritonOptions {

  /* Debug configurations */
  bool dumpStats = false;
  bool dumpTrace = false;

  /* Execution configurations */
  char *startAnalysisFromSymbol = NULL;
  std::set<uint64_t> startAnalysisFromAddr;
  std::set<uint64_t> stopAnalysisFromAddr;

  /* Taint configurations */
  std::map<uint64_t, uint64_t> taintRegFromAddr;   // <addr, reg>
  std::map<uint64_t, uint64_t> untaintRegFromAddr; // <addr, reg>
  std::map<uint64_t, uint64_t> taintMemFromAddr;   // <addr, reg>
  std::map<uint64_t, uint64_t> untaintMemFromAddr; // <addr, reg>
};


static char Triton_runProgram_doc[] = "Start the Pin instrumentation";
static PyObject* Triton_runProgram(PyObject* self, PyObject* noarg)
{
  // Never returns - Rock 'n roll baby \o/
  PIN_StartProgram();
  return Py_None;
}


static char Triton_startAnalysisFromSymbol_doc[] = "Start the symbolic execution from a specific name point";
static PyObject* Triton_startAnalysisFromSymbol(PyObject* self, PyObject* name)
{

  if (!PyString_Check(name)){
    PyErr_Format(PyExc_TypeError, "startAnalysisFromSymbol(): expected a string");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::startAnalysisFromSymbol = PyString_AsString(name);
  return Py_None;
}


static char Triton_startAnalysisFromAddr_doc[] = "Start the symbolic execution from a specific address";
static PyObject* Triton_startAnalysisFromAddr(PyObject* self, PyObject* addr)
{

  if (!PyLong_Check(addr) && !PyInt_Check(addr)){
    PyErr_Format(PyExc_TypeError, "startAnalysisFromAddr(): expected an address");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::startAnalysisFromAddr.insert(PyLong_AsLong(addr));
  return Py_None;
}


static char Triton_stopAnalysisFromAddr_doc[] = "Stop the symbolic execution from a specific address";
static PyObject* Triton_stopAnalysisFromAddr(PyObject* self, PyObject* addr)
{

  if (!PyLong_Check(addr) && !PyInt_Check(addr)){
    PyErr_Format(PyExc_TypeError, "stopAnalysisFromAddr(): expected an address");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::stopAnalysisFromAddr.insert(PyLong_AsLong(addr));
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
  {"dumpStats",               Triton_dumpStats,               METH_O,       Triton_dumpStats_doc},
  {"dumpTrace",               Triton_dumpTrace,               METH_O,       Triton_dumpTrace_doc},
  {"runProgram",              Triton_runProgram,              METH_NOARGS,  Triton_runProgram_doc},
  {"startAnalysisFromAddr",   Triton_startAnalysisFromAddr,   METH_O,       Triton_startAnalysisFromAddr_doc},
  {"startAnalysisFromSymbol", Triton_startAnalysisFromSymbol, METH_O,       Triton_startAnalysisFromSymbol_doc},
  {"stopAnalysisFromAddr",    Triton_stopAnalysisFromAddr ,   METH_O,       Triton_stopAnalysisFromAddr_doc},
  {NULL,                      NULL,                           0,            NULL}
};

