
#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>

#include "AnalysisProcessor.h"
#include "CallbackDefine.h"
#include "TritonPyObject.h"
#include "pin.H"
#include "xPyFunc.h"

extern AnalysisProcessor ap;


/* NameSapce for all Python Bindings variables */
namespace PyTritonOptions {
  /* Execution configurations */
  char                *startAnalysisFromSymbol = NULL;
  std::set<uint64_t>  startAnalysisFromAddr;
  std::set<uint64_t>  stopAnalysisFromAddr;

  /* Callback configurations */
  PyObject *callbackBefore = NULL; // Before the instruction processing
  PyObject *callbackAfter  = NULL; // After the instruction processing
  PyObject *callbackFini   = NULL; // At the end of the execution

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

  else if ((PyLong_AsLong(flag) == CB_FINI))
    PyTritonOptions::callbackFini = function;

  else {
    PyErr_Format(PyExc_TypeError, "addCallback(): expected CB_BEFORE, CB_AFTER or CB_FINI as second argument");
    PyErr_Print();
    exit(-1);
  }

  return Py_None;
}


static char Triton_convertExprToSymVar_doc[] = "Converts an expression to a symbolic variable";
static PyObject *Triton_convertExprToSymVar(PyObject *self, PyObject *args)
{
  PyObject *exprId, *symVarSize;
  uint64_t vs, ei;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &exprId, &symVarSize);

  if (!PyLong_Check(exprId) && !PyInt_Check(exprId)) {
    PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected an integer as first argument");
    PyErr_Print();
    exit(-1);
  }

  if (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)) {
    PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected an integer as second argument");
    PyErr_Print();
    exit(-1);
  }

  ei = PyLong_AsLong(exprId);
  vs = PyLong_AsLong(symVarSize);

  if (vs != 8 && vs != 4 && vs != 2 && vs != 1){
    PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): The symVarSize argument must be: 8, 4, 2 or 1");
    PyErr_Print();
    exit(-1);
  }

  ap.convertExprToSymVar(ei, vs);

  return Py_None;
}


static char Triton_getBacktrackedSymExpr_doc[] = "Returns the backtracked symbolic expression from an expression id";
static PyObject *Triton_getBacktrackedSymExpr(PyObject *self, PyObject *id)
{
  std::string backtrackedExpr;

  if (!PyLong_Check(id) && !PyInt_Check(id)){
    PyErr_Format(PyExc_TypeError, "getBacktrackedSymExpr(): expected an id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  backtrackedExpr = ap.getBacktrackedExpressionFromId(PyLong_AsLong(id));
  if (backtrackedExpr.empty())
    return Py_None;
  return Py_BuildValue("s", backtrackedExpr.c_str());
}


static char Triton_getMemSymbolicID_doc[] = "Get the symbolic memory reference";
static PyObject *Triton_getMemSymbolicID(PyObject *self, PyObject *addr)
{
  if (!PyLong_Check(addr) && !PyInt_Check(addr)){
    PyErr_Format(PyExc_TypeError, "getMemSymbolicID(): expected a memory address (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  return Py_BuildValue("k", ap.getMemSymbolicID(PyLong_AsLong(addr)));
}


static char Triton_getMemValue_doc[] = "Get the current value of the memory";
static PyObject *Triton_getMemValue(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *readSize;
  uint64_t ad;
  uint64_t rs;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &readSize);

  if (!ap.getCurrentCtxH()){
    PyErr_Format(PyExc_TypeError, "getMemValue(): Can't call getMemValue() right now. You must run the program before.");
    PyErr_Print();
    exit(-1);
  }

  if (!PyLong_Check(addr) && !PyInt_Check(addr)){
    PyErr_Format(PyExc_TypeError, "getMemValue(): expected an address (integer) as argument");
    PyErr_Print();
    exit(-1);
  }

  ad = PyLong_AsLong(addr);
  rs = PyLong_AsLong(readSize);

  if (rs != 8 && rs != 4 && rs != 2 && rs != 1){
    PyErr_Format(PyExc_TypeError, "getMemValue(): The readSize argument must be: 8, 4, 2 or 1");
    PyErr_Print();
    exit(-1);
  }

  if (PIN_CheckReadAccess(reinterpret_cast<void*>(ad)) == false){
    PyErr_Format(PyExc_TypeError, "getMemValue(): The targeted address memory can not be read");
    PyErr_Print();
    exit(-1);
  }

  return Py_BuildValue("k", ap.getMemValue(ad, rs));
}


static char Triton_getModel_doc[] = "Returns a model of the symbolic expression";
static PyObject *Triton_getModel(PyObject *self, PyObject *expr)
{
  std::list< std::pair<std::string, unsigned long long> >::iterator it;
  std::list< std::pair<std::string, unsigned long long> > models;

  if (!PyString_Check(expr)){
    PyErr_Format(PyExc_TypeError, "getModel(): expected an expression (string) as argument");
    PyErr_Print();
    exit(-1);
  }

  /* Get models */
  models = ap.getModel(PyString_AsString(expr));

  /* Craft the model dictionary */
  PyObject *modelsDict = xPyDict_New();
  for (it = models.begin() ; it != models.end(); it++)
    PyDict_SetItemString(modelsDict, it->first.c_str(), Py_BuildValue("k", it->second));

  return modelsDict;
}


static char Triton_getRegSymbolicID_doc[] = "Get the symbolic register reference";
static PyObject *Triton_getRegSymbolicID(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg)){
    PyErr_Format(PyExc_TypeError, "getMemSymbolicID(): expected a register id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  return Py_BuildValue("k", ap.getRegSymbolicID(PyLong_AsLong(reg)));
}


static char Triton_getRegValue_doc[] = "Get the current value of the register";
static PyObject *Triton_getRegValue(PyObject *self, PyObject *reg)
{
  uint64_t tritonReg;
  uint64_t pinReg;

  if (!PyLong_Check(reg) && !PyInt_Check(reg)){
    PyErr_Format(PyExc_TypeError, "getRegValue(): expected a register id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }

  if (!ap.getCurrentCtxH()){
    PyErr_Format(PyExc_TypeError, "getRegValue(): Can't call getRegValue() right now. You must run the program before.");
    PyErr_Print();
    exit(-1);
  }

  tritonReg = PyLong_AsLong(reg);
  pinReg = ap.convertTritonReg2PinReg(tritonReg);

  if (pinReg == static_cast<uint64_t>(-1)){
    PyErr_Format(PyExc_TypeError, "getRegValue(): Register ID not supported");
    PyErr_Print();
    exit(-1);
  }

  return Py_BuildValue("k", ap.getRegisterValue(pinReg));
}


static char Triton_getStats_doc[] = "Returns statistics of the execution";
static PyObject *Triton_getStats(PyObject *self, PyObject *noargs)
{
  PyObject *stats = xPyDict_New();
  PyDict_SetItemString(stats, "branches",     PyLong_FromLong(ap.getNumberOfBranchesTaken()));
  PyDict_SetItemString(stats, "expressions",  PyLong_FromLong(ap.getNumberOfExpressions()));
  PyDict_SetItemString(stats, "time",         PyLong_FromLong(ap.getTimeOfExecution()));
  PyDict_SetItemString(stats, "unknownExpr",  PyLong_FromLong(ap.getNumberOfUnknownInstruction()));
  return stats;
}


static char Triton_getSymExpr_doc[] = "Returns a SymbolicElement class corresponding to the symbolic element ID.";
static PyObject *Triton_getSymExpr(PyObject *self, PyObject *id)
{
  uint64_t        exprId;
  SymbolicElement *expr;

  if (!PyLong_Check(id) && !PyInt_Check(id)){
    PyErr_Format(PyExc_TypeError, "getSymExpr(): expected an id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }

  exprId = PyLong_AsLong(id);
  expr = ap.getElementFromId(exprId);

  if (expr == NULL)
    return Py_None;

  return PySymbolicElement(expr);
}


static char Triton_isMemTainted_doc[] = "Check if the memory is tainted";
static PyObject *Triton_isMemTainted(PyObject *self, PyObject *mem)
{
  if (!PyLong_Check(mem) && !PyInt_Check(mem)){
    PyErr_Format(PyExc_TypeError, "isMemTainted(): expected an address (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  if (ap.isMemTainted(PyInt_AsLong(mem)) == true)
    return Py_True;
  return Py_False;
}


static char Triton_isRegTainted_doc[] = "Check if the register is tainted";
static PyObject *Triton_isRegTainted(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg)){
    PyErr_Format(PyExc_TypeError, "isRegTainted(): expected a register id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  if (ap.isRegTainted(PyInt_AsLong(reg)) == true)
    return Py_True;
  return Py_False;
}


static char Triton_opcodeToString_doc[] = "Returns a string with the opcode of the instruction";
static PyObject *Triton_opcodeToString(PyObject *self, PyObject *opcode)
{
  if (!PyLong_Check(opcode) && !PyInt_Check(opcode)){
    PyErr_Format(PyExc_TypeError, "opcodeToString(): expected an opcode (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  return Py_BuildValue("s", OPCODE_StringShort(PyInt_AsLong(opcode)).c_str());
}


static char Triton_runProgram_doc[] = "Start the Pin instrumentation";
static PyObject *Triton_runProgram(PyObject *self, PyObject *noarg)
{
  // Never returns - Rock 'n roll baby \o/
  PIN_StartProgram();
  return Py_None;
}


static char Triton_saveTrace_doc[] = "Save the trace in a file";
static PyObject *Triton_saveTrace(PyObject *self, PyObject *file)
{
  if (!PyString_Check(file)){
    PyErr_Format(PyExc_TypeError, "saveTrace(): expected a string as argument");
    PyErr_Print();
    exit(-1);
  }
  std::stringstream f(PyString_AsString(file));
  ap.saveTrace(f);
  return Py_None;
}


static char Triton_setMemValue_doc[] = "Insert value in the runtime memory";
static PyObject *Triton_setMemValue(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *value;
  PyObject *writeSize;
  uint64_t ad; // address
  uint64_t va; // value
  uint64_t ws; // write size

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &addr, &writeSize, &value);

  if (!PyLong_Check(addr) && !PyInt_Check(addr)){
    PyErr_Format(PyExc_TypeError, "setMemValue(): expected an address (integer) as first argument");
    PyErr_Print();
    exit(-1);
  }

  if (!PyLong_Check(writeSize) && !PyInt_Check(writeSize)){
    PyErr_Format(PyExc_TypeError, "setMemValue(): expected an integer as second argument");
    PyErr_Print();
    exit(-1);
  }

  if (!PyLong_Check(value) && !PyInt_Check(value)){
    PyErr_Format(PyExc_TypeError, "setMemValue(): expected an integer as third argument");
    PyErr_Print();
    exit(-1);
  }

  ad = PyLong_AsLong(addr);
  ws = PyLong_AsLong(writeSize);

  if (ws != 8 && ws != 4 && ws != 2 && ws != 1){
    PyErr_Format(PyExc_TypeError, "setMemValue(): The writeSize argument must be: 8, 4, 2 or 1");
    PyErr_Print();
    exit(-1);
  }

  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(ad)) == false){
    PyErr_Format(PyExc_TypeError, "setMemValue(): Can not write into the targeted address memory");
    PyErr_Print();
    exit(-1);
  }

  va = PyLong_AsLong(value);

  switch (ws){
    case 1:
      *((char *)ad) = va; break;
      break;
    case 2:
      *((short *)ad) = va;
      break;
    case 4:
      *((uint32_t *)ad) = va;
      break;
    case 8:
      *((uint64_t *)ad) = va;
      break;
  }

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


static char Triton_taintMem_doc[] = "Taint an address memory";
static PyObject *Triton_taintMem(PyObject *self, PyObject *mem)
{
  if (!PyLong_Check(mem) && !PyInt_Check(mem)){
    PyErr_Format(PyExc_TypeError, "TaintMem(): expected a memory address (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  ap.taintMem(PyInt_AsLong(mem));
  return Py_None;
}


static char Triton_taintReg_doc[] = "Taint a register";
static PyObject *Triton_taintReg(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg)){
    PyErr_Format(PyExc_TypeError, "taintReg(): expected a register id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  ap.taintReg(PyInt_AsLong(reg));
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
      PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): The second argument must be a list of register id (integer)");
      PyErr_Print();
      exit(-1);
    }
    regsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::taintRegFromAddr.insert(std::pair<uint64_t, std::list<uint64_t>>(PyLong_AsLong(addr), regsList));
  return Py_None;
}


static char Triton_untaintMem_doc[] = "Untaint an address memory";
static PyObject *Triton_untaintMem(PyObject *self, PyObject *mem)
{
  if (!PyLong_Check(mem) && !PyInt_Check(mem)){
    PyErr_Format(PyExc_TypeError, "untaintMem(): expected a memory address (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  ap.untaintMem(PyInt_AsLong(mem));
  return Py_None;
}


static char Triton_untaintReg_doc[] = "Untaint a register";
static PyObject *Triton_untaintReg(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg)){
    PyErr_Format(PyExc_TypeError, "untaintReg(): expected a register id (integer) as argument");
    PyErr_Print();
    exit(-1);
  }
  ap.untaintReg(PyInt_AsLong(reg));
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
      PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): The second argument must be a list of register id (integer)");
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
  {"addCallback",               Triton_addCallback,               METH_VARARGS, Triton_addCallback_doc},
  {"convertExprToSymVar",       Triton_convertExprToSymVar,       METH_VARARGS, Triton_convertExprToSymVar_doc},
  {"getBacktrackedSymExpr",     Triton_getBacktrackedSymExpr,     METH_O,       Triton_getBacktrackedSymExpr_doc},
  {"getMemSymbolicID",          Triton_getMemSymbolicID,          METH_O,       Triton_getMemSymbolicID_doc},
  {"getMemValue",               Triton_getMemValue,               METH_VARARGS, Triton_getMemValue_doc},
  {"getModel",                  Triton_getModel,                  METH_O,       Triton_getModel_doc},
  {"getRegSymbolicID",          Triton_getRegSymbolicID,          METH_O,       Triton_getRegSymbolicID_doc},
  {"getRegValue",               Triton_getRegValue,               METH_O,       Triton_getRegValue_doc},
  {"getStats",                  Triton_getStats,                  METH_NOARGS,  Triton_getStats_doc},
  {"getSymExpr",                Triton_getSymExpr,                METH_O,       Triton_getSymExpr_doc},
  {"isMemTainted",              Triton_isMemTainted,              METH_O,       Triton_isMemTainted_doc},
  {"isRegTainted",              Triton_isRegTainted,              METH_O,       Triton_isRegTainted_doc},
  {"opcodeToString",            Triton_opcodeToString,            METH_O,       Triton_opcodeToString_doc},
  {"runProgram",                Triton_runProgram,                METH_NOARGS,  Triton_runProgram_doc},
  {"saveTrace",                 Triton_saveTrace,                 METH_O,       Triton_saveTrace_doc},
  {"setMemValue",               Triton_setMemValue,               METH_VARARGS, Triton_setMemValue_doc},
  {"startAnalysisFromAddr",     Triton_startAnalysisFromAddr,     METH_O,       Triton_startAnalysisFromAddr_doc},
  {"startAnalysisFromSymbol",   Triton_startAnalysisFromSymbol,   METH_O,       Triton_startAnalysisFromSymbol_doc},
  {"stopAnalysisFromAddr",      Triton_stopAnalysisFromAddr,      METH_O,       Triton_stopAnalysisFromAddr_doc},
  {"taintMem",                  Triton_taintMem,                  METH_O,       Triton_taintMem_doc},
  {"taintReg",                  Triton_taintReg,                  METH_O,       Triton_taintReg_doc},
  {"taintRegFromAddr",          Triton_taintRegFromAddr,          METH_VARARGS, Triton_taintRegFromAddr_doc},
  {"untaintMem",                Triton_untaintMem,                METH_O,       Triton_untaintMem_doc},
  {"untaintReg",                Triton_untaintReg,                METH_O,       Triton_untaintReg_doc},
  {"untaintRegFromAddr",        Triton_untaintRegFromAddr,        METH_VARARGS, Triton_untaintRegFromAddr_doc},
  {NULL,                        NULL,                             0,            NULL}
};


