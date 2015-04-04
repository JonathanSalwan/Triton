
#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>

#include "pin.H"

#define CB_BEFORE 0
#define CB_AFTER  1


/* NameSapce for all Python Bindings variables */
namespace PyTritonOptions {

  /* Debug configurations */
  bool dumpStats = false;
  bool dumpTrace = false;

  /* Execution configurations */
  char *startAnalysisFromSymbol = NULL;
  std::set<uint64_t> startAnalysisFromAddr;
  std::set<uint64_t> stopAnalysisFromAddr;

  /* Callback configurations */
  PyObject *callbackBefore = NULL; // Before the instruction processing
  PyObject *callbackAfter  = NULL; // After the instruction processing

  /* Taint configurations */
  std::map<uint64_t, std::list<uint64_t>> taintRegFromAddr;   // <addr, [reg1, reg2]>
  std::map<uint64_t, std::list<uint64_t>> untaintRegFromAddr; // <addr, [reg1, reg2]>
  std::map<uint64_t, std::list<uint64_t>> taintMemFromAddr;   // <addr, [mem1, mem2]>
  std::map<uint64_t, std::list<uint64_t>> untaintMemFromAddr; // <addr, [mem1, mem2]>
};


static char Triton_addCallback_doc[] = "Add a callback for each instruction instrumented";
static PyObject *Triton_addCallback(PyObject *self, PyObject *args)
{
  PyObject *function;
  PyObject *flag;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &function, &flag);

  if (!PyCallable_Check(function)){
    PyErr_Format(PyExc_TypeError, "addCallback(): expected a function callback as first argument");
    PyErr_Print();
    exit(-1);
  }

  /* Check if the second arg is CB_BEFORE or CB_AFTER */
  if (!PyLong_Check(flag) && !PyInt_Check(flag)) {
    PyErr_Format(PyExc_TypeError, "addCallback(): expected an integer as second argument");
    PyErr_Print();
    exit(-1);
  }

  if (PyLong_AsLong(flag) == CB_BEFORE)
    PyTritonOptions::callbackBefore = function;
  else if ((PyLong_AsLong(flag) == CB_AFTER))
    PyTritonOptions::callbackAfter = function;
  else {
    PyErr_Format(PyExc_TypeError, "addCallback(): expected CB_BEFORE or CB_AFTER as second argument");
    PyErr_Print();
    exit(-1);
  }

  return Py_None;
}


static char Triton_runProgram_doc[] = "Start the Pin instrumentation";
static PyObject *Triton_runProgram(PyObject *self, PyObject *noarg)
{
  // Never returns - Rock 'n roll baby \o/
  PIN_StartProgram();
  return Py_None;
}


static char Triton_startAnalysisFromSymbol_doc[] = "Start the symbolic execution from a specific name point";
static PyObject *Triton_startAnalysisFromSymbol(PyObject *self, PyObject *name)
{

  if (!PyString_Check(name)){
    PyErr_Format(PyExc_TypeError, "startAnalysisFromSymbol(): expected a string as argument");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::startAnalysisFromSymbol = PyString_AsString(name);
  return Py_None;
}


static char Triton_startAnalysisFromAddr_doc[] = "Start the symbolic execution from a specific address";
static PyObject *Triton_startAnalysisFromAddr(PyObject *self, PyObject *addr)
{

  if (!PyLong_Check(addr) && !PyInt_Check(addr)){
    PyErr_Format(PyExc_TypeError, "startAnalysisFromAddr(): expected an address as argument");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::startAnalysisFromAddr.insert(PyLong_AsLong(addr));
  return Py_None;
}


static char Triton_stopAnalysisFromAddr_doc[] = "Stop the symbolic execution from a specific address";
static PyObject *Triton_stopAnalysisFromAddr(PyObject *self, PyObject *addr)
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
static PyObject *Triton_dumpTrace(PyObject *self, PyObject *flag)
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
static PyObject *Triton_dumpStats(PyObject *self, PyObject *flag)
{
  if (!PyBool_Check(flag)){
    PyErr_Format(PyExc_TypeError, "dumpStats(): expected a boolean");
    PyErr_Print();
    exit(-1);
  }
  PyTritonOptions::dumpStats = (flag == Py_True);
  return Py_None;
}


static char Triton_taintRegFromAddr_doc[] = "Taint specific registers from an address";
static PyObject *Triton_taintRegFromAddr(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *regs;
  std::list<uint64_t> regsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &regs);

  /* Check if the first arg (addr) is a integer */
  if (!PyLong_Check(addr) && !PyInt_Check(addr)) {
    PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): expected an address as first argument");
    PyErr_Print();
    exit(-1);
  }

  /* Check if the second arg (regs) is a list */
  if (!PyList_Check(regs)) {
    PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): expected a list as second argument");
    PyErr_Print();
    exit(-1);
  }

  /* Check if the regs list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(regs); i++){
    PyObject *item = PyList_GetItem(regs, i);
    if (!PyLong_Check(item) && !PyInt_Check(item)){
      PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): The second argument must be a list of integer");
      PyErr_Print();
      exit(-1);
    }
    regsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::taintRegFromAddr.insert(std::pair<uint64_t, std::list<uint64_t>>(PyLong_AsLong(addr), regsList));
  return Py_None;
}


static char Triton_untaintRegFromAddr_doc[] = "Untaint specific registers from an address";
static PyObject *Triton_untaintRegFromAddr(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *regs;
  std::list<uint64_t> regsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &regs);

  /* Check if the first arg (addr) is a integer */
  if (!PyLong_Check(addr) && !PyInt_Check(addr)) {
    PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): expected an address as first argument");
    PyErr_Print();
    exit(-1);
  }

  /* Check if the second arg (regs) is a list */
  if (!PyList_Check(regs)) {
    PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): expected a list as second argument");
    PyErr_Print();
    exit(-1);
  }

  /* Check if the regs list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(regs); i++){
    PyObject *item = PyList_GetItem(regs, i);
    if (!PyLong_Check(item) && !PyInt_Check(item)){
      PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): The second argument must be a list of integer");
      PyErr_Print();
      exit(-1);
    }
    regsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::untaintRegFromAddr.insert(std::pair<uint64_t, std::list<uint64_t>>(PyLong_AsLong(addr), regsList));
  return Py_None;
}


PyMethodDef pythonCallbacks[] = {
  {"addCallback",             Triton_addCallback,             METH_VARARGS, Triton_addCallback_doc},
  {"dumpStats",               Triton_dumpStats,               METH_O,       Triton_dumpStats_doc},
  {"dumpTrace",               Triton_dumpTrace,               METH_O,       Triton_dumpTrace_doc},
  {"runProgram",              Triton_runProgram,              METH_NOARGS,  Triton_runProgram_doc},
  {"startAnalysisFromAddr",   Triton_startAnalysisFromAddr,   METH_O,       Triton_startAnalysisFromAddr_doc},
  {"startAnalysisFromSymbol", Triton_startAnalysisFromSymbol, METH_O,       Triton_startAnalysisFromSymbol_doc},
  {"stopAnalysisFromAddr",    Triton_stopAnalysisFromAddr,    METH_O,       Triton_stopAnalysisFromAddr_doc},
  {"taintRegFromAddr",        Triton_taintRegFromAddr,        METH_VARARGS, Triton_taintRegFromAddr_doc},
  {"untaintRegFromAddr",      Triton_untaintRegFromAddr,      METH_VARARGS, Triton_untaintRegFromAddr_doc},
  {NULL,                      NULL,                           0,            NULL}
};

