
#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>

#include <AnalysisProcessor.h>
#include <CallbackDefine.h>
#include <PINConverter.h>
#include <PythonUtils.h>
#include <TritonPyObject.h>
#include <Utils.h>
#include <pin.H>
#include <xPyFunc.h>

extern AnalysisProcessor ap;


/* NameSpace for all Python Bindings variables */
namespace PyTritonOptions {
  /* Execution configurations */
  char              *startAnalysisFromSymbol = nullptr;
  std::set<uint64>  startAnalysisFromAddr;
  std::set<uint64>  stopAnalysisFromAddr;

  /* Callback configurations */
  PyObject *callbackBefore        = nullptr;                // Before the instruction processing
  PyObject *callbackBeforeIRProc  = nullptr;                // Before the IR processing
  PyObject *callbackAfter         = nullptr;                // After the instruction processing
  PyObject *callbackFini          = nullptr;                // At the end of the execution
  PyObject *callbackSyscallEntry  = nullptr;                // Before syscall processing
  PyObject *callbackSyscallExit   = nullptr;                // After syscall processing
  std::map<const char *, PyObject *> callbackRoutineEntry;  // Before routine processing
  std::map<const char *, PyObject *> callbackRoutineExit;   // After routine processing

  /* Taint configurations */
  std::map<uint64, std::list<uint64>> taintRegFromAddr;   // <addr, [reg1, reg2]>
  std::map<uint64, std::list<uint64>> untaintRegFromAddr; // <addr, [reg1, reg2]>
  std::map<uint64, std::list<uint64>> taintMemFromAddr;   // <addr, [mem1, mem2]>
  std::map<uint64, std::list<uint64>> untaintMemFromAddr; // <addr, [mem1, mem2]>
};


static char Triton_addCallback_doc[] = "Adds a callback for each instruction instrumented";
static PyObject *Triton_addCallback(PyObject *self, PyObject *args)
{
  PyObject *function;
  PyObject *flag;
  PyObject *routine = nullptr;


  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &function, &flag, &routine);

  if (!PyCallable_Check(function))
    return PyErr_Format(PyExc_TypeError, "addCallback(): expected a function callback as first argument");

  /* Check if the second arg is CB_BEFORE or CB_AFTER */
  if (!PyLong_Check(flag) && !PyInt_Check(flag))
    return PyErr_Format(PyExc_TypeError, "addCallback(): expected an integer as second argument");

  if (PyLong_AsLong(flag) == CB_BEFORE)
    PyTritonOptions::callbackBefore = function;

  else if ((PyLong_AsLong(flag) == CB_BEFORE_SYMPROC))
    PyTritonOptions::callbackBeforeIRProc = function;

  else if ((PyLong_AsLong(flag) == CB_AFTER))
    PyTritonOptions::callbackAfter = function;

  else if ((PyLong_AsLong(flag) == CB_FINI))
    PyTritonOptions::callbackFini = function;

  else if ((PyLong_AsLong(flag) == CB_SYSCALL_ENTRY))
    PyTritonOptions::callbackSyscallEntry = function;

  else if ((PyLong_AsLong(flag) == CB_SYSCALL_EXIT))
    PyTritonOptions::callbackSyscallExit = function;

  else if ((PyLong_AsLong(flag) == CB_ROUTINE_ENTRY)){
    if (routine == nullptr || !PyString_Check(routine))
      return PyErr_Format(PyExc_TypeError, "addCallback(): expected a string as third argument");
    PyTritonOptions::callbackRoutineEntry.insert(std::pair<const char*,PyObject*>(PyString_AsString(routine), function));
  }

  else if ((PyLong_AsLong(flag) == CB_ROUTINE_EXIT)){
    if (routine == nullptr || !PyString_Check(routine))
      return PyErr_Format(PyExc_TypeError, "addCallback(): expected a string as third argument");
    PyTritonOptions::callbackRoutineExit.insert(std::pair<const char*,PyObject*>(PyString_AsString(routine), function));
  }

  else
    return PyErr_Format(PyExc_TypeError, "addCallback(): expected an IDREF.CALLBACK as second argument");

  return Py_None;
}


static char Triton_checkReadAccess_doc[] = "Checks whether the memory page which contains this address has a read access protection";
static PyObject *Triton_checkReadAccess(PyObject *self, PyObject *addr)
{
  uint64 ad;

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "checkReadAccess(): expected an address (integer) as argument");

  ad = PyLong_AsLong(addr);
  if (PIN_CheckReadAccess(reinterpret_cast<void*>(ad)) == true)
    return Py_True;

  return Py_False;
}


static char Triton_checkWriteAccess_doc[] = "Checks whether the memory page which contains this address has a write access protection";
static PyObject *Triton_checkWriteAccess(PyObject *self, PyObject *addr)
{
  uint64 ad;

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "checkWriteAccess(): expected an address (integer) as argument");

  ad = PyLong_AsLong(addr);
  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(ad)) == true)
    return Py_True;

  return Py_False;
}


static char Triton_concretizeMem_doc[] = "Concretize a memory reference";
static PyObject *Triton_concretizeMem(PyObject *self, PyObject *addr)
{
  uint64 ad;

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "concretizeMem(): expected an address (integer) as argument");

  ad = PyLong_AsLong(addr);
  ap.concretizeMem(ad);
  return Py_None;
}


static char Triton_concretizeReg_doc[] = "Concretize a register reference";
static PyObject *Triton_concretizeReg(PyObject *self, PyObject *regId)
{
  uint64 reg;

  if (!PyLong_Check(regId) && !PyInt_Check(regId))
    return PyErr_Format(PyExc_TypeError, "concretizeReg(): expected a IDREF.REG as argument");

  reg = PyLong_AsLong(regId);
  ap.concretizeReg(reg);
  return Py_None;
}


static char Triton_convertExprToSymVar_doc[] = "Converts an expression to a symbolic variable";
static PyObject *Triton_convertExprToSymVar(PyObject *self, PyObject *args)
{
  PyObject *exprId, *symVarSize, *varComment = nullptr;
  uint64 vs, ei;
  std::string vc;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &exprId, &symVarSize, &varComment);

  if (varComment == nullptr)
    varComment = PyString_FromString("");

  if (!PyLong_Check(exprId) && !PyInt_Check(exprId))
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected an integer as first argument");

  if (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize))
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected an integer as second argument");

  if (!PyString_Check(varComment))
      return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected a comment (string) as third argument");

  ei = PyLong_AsLong(exprId);
  vs = PyLong_AsLong(symVarSize);
  vc = PyString_AsString(varComment);

  if (vs != DQWORD_SIZE && vs != QWORD_SIZE && vs != DWORD_SIZE && vs != WORD_SIZE && vs != BYTE_SIZE)
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): The symVarSize argument must be: DQWORD, QWORD, DWORD, WORD or BYTE");

  return Py_BuildValue("k", ap.convertExprToSymVar(ei, vs, vc));
}


static char Triton_convertMemToSymVar_doc[] = "Converts a memory address to a symbolic variable";
static PyObject *Triton_convertMemToSymVar(PyObject *self, PyObject *args)
{
  PyObject *memAddr, *symVarSize, *varComment = nullptr;
  uint64 vs, ma;
  std::string vc;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &memAddr, &symVarSize, &varComment);

  if (varComment == nullptr)
    varComment = PyString_FromString("");

  if (!PyLong_Check(memAddr) && !PyInt_Check(memAddr))
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): expected a memory address as first argument");

  if (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize))
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): expected a size as second argument");

  if (!PyString_Check(varComment))
      return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): expected a comment (string) as third argument");

  ma = PyLong_AsLong(memAddr);
  vs = PyLong_AsLong(symVarSize);
  vc = PyString_AsString(varComment);

  if (vs != DQWORD_SIZE && vs != QWORD_SIZE && vs != DWORD_SIZE && vs != WORD_SIZE && vs != BYTE_SIZE)
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): The symVarSize argument must be: DQWORD, QWORD, DWORD, WORD or BYTE");

  return Py_BuildValue("k", ap.convertMemToSymVar(ma, vs, vc));
}


static char Triton_convertRegToSymVar_doc[] = "Converts a register to a symbolic variable";
static PyObject *Triton_convertRegToSymVar(PyObject *self, PyObject *args)
{
  PyObject *regId, *symVarSize, *varComment = nullptr;
  uint64 vs, ri;
  std::string vc;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &regId, &symVarSize, &varComment);

  if (varComment == nullptr)
    varComment = PyString_FromString("");

  if (!PyLong_Check(regId) && !PyInt_Check(regId))
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): expected a IDREF.REG as first argument");

  if (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize))
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): expected a size as second argument");

  if (!PyString_Check(varComment))
      return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): expected a comment (string) as third argument");

  ri = PyLong_AsLong(regId);
  vs = PyLong_AsLong(symVarSize);
  vc = PyString_AsString(varComment);

  if (vs != DQWORD_SIZE && vs != QWORD_SIZE && vs != DWORD_SIZE && vs != WORD_SIZE && vs != BYTE_SIZE)
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): The symVarSize argument must be: DQWORD, QWORD, DWORD, WORD or BYTE");

  return Py_BuildValue("k", ap.convertRegToSymVar(ri, vs, vc));
}


static char Triton_disableSnapshot_doc[] = "Disables the snapshot engine";
static PyObject *Triton_disableSnapshot(PyObject *self, PyObject *noarg)
{
  ap.disableSnapshot();
  return Py_None;
}


static char Triton_getBacktrackedSymExpr_doc[] = "Returns the backtracked symbolic expression from an expression id";
static PyObject *Triton_getBacktrackedSymExpr(PyObject *self, PyObject *id)
{
  std::string backtrackedExpr;

  if (!PyLong_Check(id) && !PyInt_Check(id))
    return PyErr_Format(PyExc_TypeError, "getBacktrackedSymExpr(): expected an id (integer) as argument");

  backtrackedExpr = ap.getBacktrackedExpressionFromId(PyLong_AsLong(id));
  if (backtrackedExpr.empty())
    return Py_None;

  return Py_BuildValue("s", backtrackedExpr.c_str());
}


static char Triton_getMemSymbolicID_doc[] = "Gets the symbolic memory reference";
static PyObject *Triton_getMemSymbolicID(PyObject *self, PyObject *addr)
{
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "getMemSymbolicID(): expected a memory address (integer) as argument");

  return Py_BuildValue("k", ap.getMemSymbolicID(PyLong_AsLong(addr)));
}


static char Triton_getMemValue_doc[] = "Gets the current value of the memory";
static PyObject *Triton_getMemValue(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *readSize;
  uint64 ad;
  uint64 rs;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &readSize);

  if (!ap.getCurrentCtxH())
    return PyErr_Format(PyExc_TypeError, "getMemValue(): Can't call getMemValue() right now. You must run the program before.");

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "getMemValue(): expected an address (integer) as argument");

  ad = PyLong_AsLong(addr);
  rs = PyLong_AsLong(readSize);

  if (rs != DQWORD_SIZE && rs != QWORD_SIZE && rs != DWORD_SIZE && rs != WORD_SIZE && rs != BYTE_SIZE)
    return PyErr_Format(PyExc_TypeError, "getMemValue(): The readSize argument must be: DQWORD, QWORD, DWORD, WORD or BYTE");

  if (PIN_CheckReadAccess(reinterpret_cast<void*>(ad)) == false)
    return PyErr_Format(PyExc_TypeError, "getMemValue(): The targeted address memory can not be read");

  /* If this is a 128-bits read size, we must use uint128ToPyLongObject() */
  if (rs == DQWORD_SIZE){
    uint128 value = ap.getMemValue(ad, rs);
    return uint128ToPyLongObject(value);
  }

  return Py_BuildValue("k", ap.getMemValue(ad, rs));
}


static char Triton_getModel_doc[] = "Returns a model of the symbolic expression";
static PyObject *Triton_getModel(PyObject *self, PyObject *expr)
{
  std::list< std::pair<std::string, unsigned long long> >::iterator it;
  std::list< std::pair<std::string, unsigned long long> > models;

  if (!PyString_Check(expr))
    return PyErr_Format(PyExc_TypeError, "getModel(): expected an expression (string) as argument");

  /* Get models */
  models = ap.getModel(PyString_AsString(expr));

  /* Craft the model dictionary */
  PyObject *modelsDict = xPyDict_New();
  for (it = models.begin() ; it != models.end(); it++)
    PyDict_SetItemString(modelsDict, it->first.c_str(), Py_BuildValue("k", it->second));

  return modelsDict;
}


static char Triton_getPathConstraints_doc[] = "Returns the list of path constraints";
static PyObject *Triton_getPathConstraints(PyObject *self, PyObject *noargs)
{
  PyObject                        *ppc;
  std::list<uint64>               pc;
  std::list<uint64>::iterator     it;
  Py_ssize_t                      size = 0;

  pc    = ap.getPathConstraints();
  size  = pc.size();
  ppc   = xPyList_New(size);

  Py_ssize_t index = 0;
  for (it = pc.begin(); it != pc.end(); it++){
    PyList_SetItem(ppc, index, Py_BuildValue("k", *it));
    index += 1;
  }

  return ppc;
}


static char Triton_getRegName_doc[] = "Gets the register name";
static PyObject *Triton_getRegName(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "getRegName(): expected a register id (integer) as argument");

  return Py_BuildValue("s", PINConverter::getRegisterName(PyLong_AsLong(reg)).c_str());
}


static char Triton_getRegSymbolicID_doc[] = "Gets the symbolic register reference";
static PyObject *Triton_getRegSymbolicID(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "getRegSymbolicID(): expected a register id (integer) as argument");

  return Py_BuildValue("k", ap.getRegSymbolicID(PyLong_AsLong(reg)));
}


static char Triton_getRegValue_doc[] = "Gets the current value of the register";
static PyObject *Triton_getRegValue(PyObject *self, PyObject *reg)
{
  uint64 tritonReg;

  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "getRegValue(): expected a register id (IDREF.REG) as argument");

  if (!ap.getCurrentCtxH())
    return PyErr_Format(PyExc_TypeError, "getRegValue(): Can't call getRegValue() right now. You must run the program before.");

  tritonReg = PyLong_AsLong(reg);

  if (tritonReg >= ID_XMM0 && tritonReg <= ID_XMM15){
    uint128 value = ap.getSSERegisterValue(tritonReg);
    return uint128ToPyLongObject(value);
  }

  return Py_BuildValue("k", ap.getRegisterValue(tritonReg));
}


static char Triton_getFlagValue_doc[] = "Gets the current value of the flag";
static PyObject *Triton_getFlagValue(PyObject *self, PyObject *flag)
{
  uint64 tritonFlag;

  if (!PyLong_Check(flag) && !PyInt_Check(flag))
    return PyErr_Format(PyExc_TypeError, "getFlagValue(): expected a flag id (IDREF.FLAG) as argument");

  if (!ap.getCurrentCtxH())
    return PyErr_Format(PyExc_TypeError, "getFlagValue(): Can't call getFlagValue() right now. You must run the program before.");

  tritonFlag = PyLong_AsLong(flag);

  return Py_BuildValue("k", ap.getFlagValue(tritonFlag));
}


static char Triton_getRegs_doc[] = "Returns informations about all registers";
static PyObject *Triton_getRegs(PyObject *self, PyObject *noargs)
{
  PyObject *regs = xPyDict_New();

  /* Build all Registers */
  for (uint64 regId = ID_RAX; regId < ID_RFLAGS; regId++){
    PyObject *reg = xPyDict_New();
    if (regId >= ID_XMM0 && regId <= ID_XMM15)
      PyDict_SetItemString(reg, "concreteValue", uint128ToPyLongObject(ap.getSSERegisterValue(regId)));
    else
      PyDict_SetItemString(reg, "concreteValue", Py_BuildValue("k", ap.getRegisterValue(regId)));
    PyDict_SetItemString(reg, "symbolicExpr", Py_BuildValue("k", ap.getRegSymbolicID(regId)));
    PyDict_SetItem(regs, Py_BuildValue("k", regId), reg);
  }

  /* Build all Flags */
  for (uint64 flagId = ID_AF; flagId <= ID_ZF; flagId++){
    PyObject *flag = xPyDict_New();
    PyDict_SetItemString(flag, "concreteValue", Py_BuildValue("k", ap.getFlagValue(flagId)));
    PyDict_SetItemString(flag, "symbolicExpr", Py_BuildValue("k", ap.getRegSymbolicID(flagId)));
    PyDict_SetItem(regs, Py_BuildValue("k", flagId), flag);
  }

  return regs;
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
  uint64          exprId;
  SymbolicElement *expr;

  if (!PyLong_Check(id) && !PyInt_Check(id))
    return PyErr_Format(PyExc_TypeError, "getSymExpr(): expected an id (integer) as argument");

  exprId = PyLong_AsLong(id);
  expr = ap.getElementFromId(exprId);

  if (expr == nullptr)
    return PyErr_Format(PyExc_TypeError, "getSymExpr(): Invalid symbolic expression ID");

  return PySymbolicElement(expr);
}


static char Triton_getSymVar_doc[] = "Returns the symbolic variable class";
static PyObject *Triton_getSymVar(PyObject *self, PyObject *symVarPy)
{
  SymbolicVariable *symVar;

  if (!PyLong_Check(symVarPy) && !PyInt_Check(symVarPy) && !PyString_Check(symVarPy))
    return PyErr_Format(PyExc_TypeError, "getSymVar(): expected a symbolic variable ID or a symbolic variable name");

  if (PyLong_Check(symVarPy) || PyInt_Check(symVarPy))
    symVar = ap.getSymVar(PyLong_AsLong(symVarPy));
  else
    symVar = ap.getSymVar(PyString_AsString(symVarPy));

  if (symVar == nullptr)
    return PyErr_Format(PyExc_TypeError, "getSymVar(): Invalid symbolic variable ID");

  return PySymbolicVariable(symVar);
}


static char Triton_getSymVarSize_doc[] = "Returns the size of the symbolic variable";
static PyObject *Triton_getSymVarSize(PyObject *self, PyObject *symVarPy)
{
  SymbolicVariable *symVar;

  if (!PyLong_Check(symVarPy) && !PyInt_Check(symVarPy) && !PyString_Check(symVarPy))
    return PyErr_Format(PyExc_TypeError, "getSymVarSize(): expected a symbolic variable ID or a symbolic variable name");

  if (PyLong_Check(symVarPy) || PyInt_Check(symVarPy))
    symVar = ap.getSymVar(PyLong_AsLong(symVarPy));
  else
    symVar = ap.getSymVar(PyString_AsString(symVarPy));

  if (symVar == nullptr)
    return PyErr_Format(PyExc_TypeError, "getSymVarSize(): Invalid symbolic variable ID");

  return Py_BuildValue("k", symVar->getSymVarSize());
}


static char Triton_getSymVars_doc[] = "Returns the list of symbolic variables";
static PyObject *Triton_getSymVars(PyObject *self, PyObject *noArg)
{
  std::vector<SymbolicVariable *> symVars;
  std::vector<SymbolicVariable *>::iterator it;
  PyObject *symVarsList;

  symVars = ap.getSymVars();
  symVarsList = xPyList_New(symVars.size());

  Py_ssize_t index = 0;
  for (it = symVars.begin(); it != symVars.end(); it++){
    PyList_SetItem(symVarsList, index, PySymbolicVariable(*it));
    index += 1;
  }

  return symVarsList;
}


static char Triton_getSyscallArgument_doc[] = "Returns the syscall argument.";
static PyObject *Triton_getSyscallArgument(PyObject *self, PyObject *args)
{
  PyObject *num;
  PyObject *std;
  uint64 ret;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &std, &num);

  if (!PyLong_Check(std) && !PyInt_Check(std))
    return PyErr_Format(PyExc_TypeError, "getSyscallArgument(): expected an id (integer) as first argument");

  if (!PyLong_Check(num) && !PyInt_Check(num))
    return PyErr_Format(PyExc_TypeError, "getSyscallArgument(): expected an id (integer) as second argument");

  LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(PyLong_AsLong(std));;
  CONTEXT *ctx = static_cast<CONTEXT*>(ap.getCurrentCtxH()->getCtx());

  ret = PIN_GetSyscallArgument(ctx, standard, PyLong_AsLong(num));

  return PyLong_FromLong(ret);
}


static char Triton_getSyscallNumber_doc[] = "Returns the syscall number. This function must be called inside the syscall entry callback. Otherwise returns results in undefined behavior.";
static PyObject *Triton_getSyscallNumber(PyObject *self, PyObject *std)
{
  uint64 syscallNumber;

  if (!PyLong_Check(std) && !PyInt_Check(std))
    return PyErr_Format(PyExc_TypeError, "getSyscallNumber(): expected an id (integer) as argument");

  LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(PyLong_AsLong(std));;
  CONTEXT *ctx = static_cast<CONTEXT*>(ap.getCurrentCtxH()->getCtx());

  syscallNumber = PIN_GetSyscallNumber(ctx, standard);

  return PyLong_FromLong(syscallNumber);
}


static char Triton_getSyscallReturn_doc[] = "Returns the syscall return value.";
static PyObject *Triton_getSyscallReturn(PyObject *self, PyObject *std)
{
  uint64 ret;

  if (!PyLong_Check(std) && !PyInt_Check(std))
    return PyErr_Format(PyExc_TypeError, "getSyscallReturn(): expected an id (integer) as argument");

  LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(PyLong_AsLong(std));;
  CONTEXT *ctx = static_cast<CONTEXT*>(ap.getCurrentCtxH()->getCtx());

  ret = PIN_GetSyscallReturn(ctx, standard);

  return PyLong_FromLong(ret);
}


static char Triton_isMemTainted_doc[] = "Checks if the memory is tainted";
static PyObject *Triton_isMemTainted(PyObject *self, PyObject *mem)
{
  if (!PyLong_Check(mem) && !PyInt_Check(mem))
    return PyErr_Format(PyExc_TypeError, "isMemTainted(): expected an address (integer) as argument");

  if (ap.isMemTainted(PyInt_AsLong(mem)) == true)
    return Py_True;

  return Py_False;
}


static char Triton_isRegTainted_doc[] = "Checks if the register is tainted";
static PyObject *Triton_isRegTainted(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "isRegTainted(): expected a register id (integer) as argument");

  if (ap.isRegTainted(PyInt_AsLong(reg)) == true)
    return Py_True;

  return Py_False;
}


static char Triton_isSnapshotEnable_doc[] = "Returns true if the snapshot is enable";
static PyObject *Triton_isSnapshotEnable(PyObject *self, PyObject *noarg)
{
  if (ap.isSnapshotEnable() == true)
    return Py_True;
  return Py_False;
}


static char Triton_opcodeToString_doc[] = "Returns a string with the opcode of the instruction";
static PyObject *Triton_opcodeToString(PyObject *self, PyObject *opcode)
{
  if (!PyLong_Check(opcode) && !PyInt_Check(opcode))
    return PyErr_Format(PyExc_TypeError, "opcodeToString(): expected an opcode (integer) as argument");

  return Py_BuildValue("s", OPCODE_StringShort(PyInt_AsLong(opcode)).c_str());
}


static char Triton_restoreSnapshot_doc[] = "Restores the last snapshot";
static PyObject *Triton_restoreSnapshot(PyObject *self, PyObject *noarg)
{
  ap.restoreSnapshot();
  return Py_None;
}


static char Triton_runProgram_doc[] = "Starts the Pin instrumentation";
static PyObject *Triton_runProgram(PyObject *self, PyObject *noarg)
{
  // Never returns - Rock 'n roll baby \o/
  PIN_StartProgram();
  return Py_None;
}


static char Triton_saveTrace_doc[] = "Saves the trace in a file";
static PyObject *Triton_saveTrace(PyObject *self, PyObject *file)
{
  if (!PyString_Check(file))
    return PyErr_Format(PyExc_TypeError, "saveTrace(): expected a string as argument");

  std::stringstream f(PyString_AsString(file));
  ap.saveTrace(f);

  return Py_None;
}


static char Triton_setMemValue_doc[] = "Inserts value into the runtime memory";
static PyObject *Triton_setMemValue(PyObject *self, PyObject *args)
{
  PyObject  *addr;
  PyObject  *value;
  PyObject  *writeSize;
  uint128   va; // value
  uint64    ad; // address
  uint64    ws; // write size

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O|O", &addr, &writeSize, &value);

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "setMemValue(): expected an address (integer) as first argument");

  if (!PyLong_Check(writeSize) && !PyInt_Check(writeSize))
    return PyErr_Format(PyExc_TypeError, "setMemValue(): expected an integer as second argument");

  if (!PyLong_Check(value) && !PyInt_Check(value))
    return PyErr_Format(PyExc_TypeError, "setMemValue(): expected an integer as third argument");

  ad = PyLong_AsLong(addr);
  ws = PyLong_AsLong(writeSize);

  if (ws != DQWORD_SIZE && ws != QWORD_SIZE && ws != DWORD_SIZE && ws != WORD_SIZE && ws != BYTE_SIZE)
    return PyErr_Format(PyExc_TypeError, "setMemValue(): The writeSize argument must be: DQWORD, QWORD, DWORD, WORD or BYTE");

  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(ad)) == false)
    return PyErr_Format(PyExc_TypeError, "setMemValue(): Can not write into the targeted address memory");

  va = PyLongObjectToUint128(value);
  ap.setMemValue(ad, ws, va);

  return Py_None;
}


static char Triton_setRegValue_doc[] = "Inserts value into the current context register";
static PyObject *Triton_setRegValue(PyObject *self, PyObject *args)
{
  PyObject *reg;
  PyObject *value;
  uint128  va;
  uint64   tr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &reg, &value);

  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "setRegValue(): expected an IDREF.REG as first argument");

  if (!PyLong_Check(value) && !PyInt_Check(value))
    return PyErr_Format(PyExc_TypeError, "setRegValue(): expected an integer as second argument");

  va = PyLongObjectToUint128(value);
  tr = PyLong_AsLong(reg);

  if (tr >= ID_XMM0 && tr <= ID_XMM15)
    ap.setSSERegisterValue(tr, va);
  else
    ap.setRegisterValue(tr, va);

  return Py_None;
}


static char Triton_startAnalysisFromSymbol_doc[] = "Starts the symbolic execution from a specific name point";
static PyObject *Triton_startAnalysisFromSymbol(PyObject *self, PyObject *name)
{

  if (!PyString_Check(name))
    return PyErr_Format(PyExc_TypeError, "startAnalysisFromSymbol(): expected a string as argument");

  PyTritonOptions::startAnalysisFromSymbol = PyString_AsString(name);
  return Py_None;
}


static char Triton_startAnalysisFromAddr_doc[] = "Starts the symbolic execution from a specific address";
static PyObject *Triton_startAnalysisFromAddr(PyObject *self, PyObject *addr)
{
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "startAnalysisFromAddr(): expected an address as argument");

  PyTritonOptions::startAnalysisFromAddr.insert(PyLong_AsLong(addr));
  return Py_None;
}


static char Triton_stopAnalysisFromAddr_doc[] = "Stops the symbolic execution from a specific address";
static PyObject *Triton_stopAnalysisFromAddr(PyObject *self, PyObject *addr)
{
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "stopAnalysisFromAddr(): expected an address");

  PyTritonOptions::stopAnalysisFromAddr.insert(PyLong_AsLong(addr));
  return Py_None;
}


static char Triton_syscallToString_doc[] = "Returns the syscall string from a syscall number";
static PyObject *Triton_syscallToString(PyObject *self, PyObject *args)
{
  PyObject *std;
  PyObject *num;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &std, &num);

  if (!PyLong_Check(std) && !PyInt_Check(std))
    return PyErr_Format(PyExc_TypeError, "syscallToString(): expected a standard IDREF.SYSCALL as first argument");

  if (!PyLong_Check(num) && !PyInt_Check(num))
    return PyErr_Format(PyExc_TypeError, "syscallToString(): expected a syscall number (integer) as second argument");

  const char *syscall = nullptr;
  switch (PyLong_AsLong(std)){
    case SYSCALL_STANDARD_IA32E_LINUX:
      syscall = syscallNumberLinux64ToString(PyLong_AsLong(num));
      break;
    default:
      return PyErr_Format(PyExc_TypeError, "syscallToString(): IDREF.SYSCALL standard unsupported");
  }

  if (syscall == nullptr)
    return PyErr_Format(PyExc_TypeError, "syscallToString(): IDREF.SYSCALL number unsupported");

  return Py_BuildValue("s", syscall);
}


static char Triton_taintMem_doc[] = "Taints an address memory";
static PyObject *Triton_taintMem(PyObject *self, PyObject *mem)
{
  if (!PyLong_Check(mem) && !PyInt_Check(mem))
    return PyErr_Format(PyExc_TypeError, "TaintMem(): expected a memory address (integer) as argument");

  ap.taintMem(PyInt_AsLong(mem));
  return Py_None;
}

static char Triton_taintMemFromAddr_doc[] = "Taints specific memory address from an address";
static PyObject *Triton_taintMemFromAddr(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *mems;
  std::list<uint64> memsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &mems);

  /* Check if the first arg (addr) is a integer */
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "taintMemFromAddr(): expected an address as first argument");

  /* Check if the second arg (mems) is a list */
  if (!PyList_Check(mems))
    return PyErr_Format(PyExc_TypeError, "taintMemFromAddr(): expected a list as second argument");

  /* Check if the mems list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(mems); i++){
    PyObject *item = PyList_GetItem(mems, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "taintMemFromAddr(): The second argument must be a list of addresses (integer)");

    memsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::taintMemFromAddr.insert(std::pair<uint64, std::list<uint64>>(PyLong_AsLong(addr), memsList));
  return Py_None;
}



static char Triton_taintReg_doc[] = "Taints a register";
static PyObject *Triton_taintReg(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "taintReg(): expected a register id (integer) as argument");

  ap.taintReg(PyInt_AsLong(reg));
  return Py_None;
}


static char Triton_taintRegFromAddr_doc[] = "Taints specific registers from an address";
static PyObject *Triton_taintRegFromAddr(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *regs;
  std::list<uint64> regsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &regs);

  /* Check if the first arg (addr) is a integer */
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): expected an address as first argument");

  /* Check if the second arg (regs) is a list */
  if (!PyList_Check(regs))
    return PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): expected a list as second argument");

  /* Check if the regs list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(regs); i++){
    PyObject *item = PyList_GetItem(regs, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): The second argument must be a list of register id (integer)");

    regsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::taintRegFromAddr.insert(std::pair<uint64, std::list<uint64>>(PyLong_AsLong(addr), regsList));
  return Py_None;
}




static char Triton_takeSnapshot_doc[] = "Takes a snapshot of the registers states and memory";
static PyObject *Triton_takeSnapshot(PyObject *self, PyObject *noarg)
{
  ap.takeSnapshot();
  return Py_None;
}


static char Triton_untaintMem_doc[] = "Untaints an address memory";
static PyObject *Triton_untaintMem(PyObject *self, PyObject *mem)
{
  if (!PyLong_Check(mem) && !PyInt_Check(mem))
    return PyErr_Format(PyExc_TypeError, "untaintMem(): expected a memory address (integer) as argument");

  ap.untaintMem(PyInt_AsLong(mem));
  return Py_None;
}

static char Triton_untaintMemFromAddr_doc[] = "Untaints specific memory addresses from an address";
static PyObject *Triton_untaintMemFromAddr(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *mems;
  std::list<uint64> memsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &mems);

  /* Check if the first arg (addr) is a integer */
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "untaintMemFromAddr(): expected an address as first argument");

  /* Check if the second arg (mems) is a list */
  if (!PyList_Check(mems))
    return PyErr_Format(PyExc_TypeError, "untaintMemFromAddr(): expected a list as second argument");

  /* Check if the mems list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(mems); i++){
    PyObject *item = PyList_GetItem(mems, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "untaintMemFromAddr(): The second argument must be a list of register id (integer)");

    memsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::untaintMemFromAddr.insert(std::pair<uint64, std::list<uint64>>(PyLong_AsLong(addr), memsList));

  return Py_None;
}



static char Triton_untaintReg_doc[] = "Untaints a register";
static PyObject *Triton_untaintReg(PyObject *self, PyObject *reg)
{
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "untaintReg(): expected a register id (integer) as argument");

  ap.untaintReg(PyInt_AsLong(reg));
  return Py_None;
}


static char Triton_untaintRegFromAddr_doc[] = "Untaints specific registers from an address";
static PyObject *Triton_untaintRegFromAddr(PyObject *self, PyObject *args)
{
  PyObject *addr;
  PyObject *regs;
  std::list<uint64> regsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "O|O", &addr, &regs);

  /* Check if the first arg (addr) is a integer */
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): expected an address as first argument");

  /* Check if the second arg (regs) is a list */
  if (!PyList_Check(regs))
    return PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): expected a list as second argument");

  /* Check if the regs list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(regs); i++){
    PyObject *item = PyList_GetItem(regs, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): The second argument must be a list of register id (integer)");

    regsList.push_back(PyLong_AsLong(item));
  }

  /* Update taint configuration */
  PyTritonOptions::untaintRegFromAddr.insert(std::pair<uint64, std::list<uint64>>(PyLong_AsLong(addr), regsList));

  return Py_None;
}




PyMethodDef tritonCallbacks[] = {
  {"addCallback",               Triton_addCallback,               METH_VARARGS, Triton_addCallback_doc},
  {"checkReadAccess",           Triton_checkReadAccess,           METH_O,       Triton_checkReadAccess_doc},
  {"checkWriteAccess",          Triton_checkWriteAccess,          METH_O,       Triton_checkWriteAccess_doc},
  {"concretizeMem",             Triton_concretizeMem,             METH_O,       Triton_concretizeMem_doc},
  {"concretizeReg",             Triton_concretizeReg,             METH_O,       Triton_concretizeReg_doc},
  {"convertExprToSymVar",       Triton_convertExprToSymVar,       METH_VARARGS, Triton_convertExprToSymVar_doc},
  {"convertMemToSymVar",        Triton_convertMemToSymVar,        METH_VARARGS, Triton_convertMemToSymVar_doc},
  {"convertRegToSymVar",        Triton_convertRegToSymVar,        METH_VARARGS, Triton_convertRegToSymVar_doc},
  {"disableSnapshot",           Triton_disableSnapshot,           METH_NOARGS,  Triton_disableSnapshot_doc},
  {"getBacktrackedSymExpr",     Triton_getBacktrackedSymExpr,     METH_O,       Triton_getBacktrackedSymExpr_doc},
  {"getFlagValue",              Triton_getFlagValue,              METH_O,       Triton_getFlagValue_doc},
  {"getMemSymbolicID",          Triton_getMemSymbolicID,          METH_O,       Triton_getMemSymbolicID_doc},
  {"getMemValue",               Triton_getMemValue,               METH_VARARGS, Triton_getMemValue_doc},
  {"getModel",                  Triton_getModel,                  METH_O,       Triton_getModel_doc},
  {"getPathConstraints",        Triton_getPathConstraints,        METH_NOARGS,  Triton_getPathConstraints_doc},
  {"getRegName",                Triton_getRegName,                METH_O,       Triton_getRegName_doc},
  {"getRegSymbolicID",          Triton_getRegSymbolicID,          METH_O,       Triton_getRegSymbolicID_doc},
  {"getRegValue",               Triton_getRegValue,               METH_O,       Triton_getRegValue_doc},
  {"getRegs",                   Triton_getRegs,                   METH_NOARGS,  Triton_getRegs_doc},
  {"getStats",                  Triton_getStats,                  METH_NOARGS,  Triton_getStats_doc},
  {"getSymExpr",                Triton_getSymExpr,                METH_O,       Triton_getSymExpr_doc},
  {"getSymVar",                 Triton_getSymVar,                 METH_O,       Triton_getSymVar_doc},
  {"getSymVarSize",             Triton_getSymVarSize,             METH_O,       Triton_getSymVarSize_doc},
  {"getSymVars",                Triton_getSymVars,                METH_NOARGS,  Triton_getSymVars_doc},
  {"getSyscallArgument",        Triton_getSyscallArgument,        METH_VARARGS, Triton_getSyscallArgument_doc},
  {"getSyscallNumber",          Triton_getSyscallNumber,          METH_O,       Triton_getSyscallNumber_doc},
  {"getSyscallReturn",          Triton_getSyscallReturn,          METH_O,       Triton_getSyscallReturn_doc},
  {"isMemTainted",              Triton_isMemTainted,              METH_O,       Triton_isMemTainted_doc},
  {"isRegTainted",              Triton_isRegTainted,              METH_O,       Triton_isRegTainted_doc},
  {"isSnapshotEnable",          Triton_isSnapshotEnable,          METH_NOARGS,  Triton_isSnapshotEnable_doc},
  {"opcodeToString",            Triton_opcodeToString,            METH_O,       Triton_opcodeToString_doc},
  {"restoreSnapshot",           Triton_restoreSnapshot,           METH_NOARGS,  Triton_restoreSnapshot_doc},
  {"runProgram",                Triton_runProgram,                METH_NOARGS,  Triton_runProgram_doc},
  {"saveTrace",                 Triton_saveTrace,                 METH_O,       Triton_saveTrace_doc},
  {"setMemValue",               Triton_setMemValue,               METH_VARARGS, Triton_setMemValue_doc},
  {"setRegValue",               Triton_setRegValue,               METH_VARARGS, Triton_setRegValue_doc},
  {"startAnalysisFromAddr",     Triton_startAnalysisFromAddr,     METH_O,       Triton_startAnalysisFromAddr_doc},
  {"startAnalysisFromSymbol",   Triton_startAnalysisFromSymbol,   METH_O,       Triton_startAnalysisFromSymbol_doc},
  {"stopAnalysisFromAddr",      Triton_stopAnalysisFromAddr,      METH_O,       Triton_stopAnalysisFromAddr_doc},
  {"syscallToString",           Triton_syscallToString,           METH_VARARGS, Triton_syscallToString_doc},
  {"taintMem",                  Triton_taintMem,                  METH_O,       Triton_taintMem_doc},
  {"taintMemFromAddr",          Triton_taintMemFromAddr,          METH_VARARGS, Triton_taintMemFromAddr_doc},
  {"taintReg",                  Triton_taintReg,                  METH_O,       Triton_taintReg_doc},
  {"taintRegFromAddr",          Triton_taintRegFromAddr,          METH_VARARGS, Triton_taintRegFromAddr_doc},
  {"takeSnapshot",              Triton_takeSnapshot,              METH_NOARGS,  Triton_takeSnapshot_doc},
  {"untaintMem",                Triton_untaintMem,                METH_O,       Triton_untaintMem_doc},
  {"untaintMemFromAddr",        Triton_untaintMemFromAddr,        METH_VARARGS, Triton_untaintMemFromAddr_doc},
  {"untaintReg",                Triton_untaintReg,                METH_O,       Triton_untaintReg_doc},
  {"untaintRegFromAddr",        Triton_untaintRegFromAddr,        METH_VARARGS, Triton_untaintRegFromAddr_doc},
  {nullptr,                     nullptr,                          0,            nullptr}
};


