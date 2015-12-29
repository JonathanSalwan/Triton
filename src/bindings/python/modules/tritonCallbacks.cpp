/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <list>
#include <map>
#include <python2.7/Python.h>
#include <set>

#include <AnalysisProcessor.h>
#include <CallbackDefine.h>
#include <MemoryOperand.h>
#include <PINConverter.h>
#include <PythonUtils.h>
#include <Registers.h>
#include <Smodel.h>
#include <Trigger.h>
#include <TritonPyObject.h>
#include <Utils.h>
#include <pin.H>
#include <xPyFunc.h>

extern AnalysisProcessor  ap;
extern Trigger            analysisTrigger;



/* NameSpace for all Python Bindings variables */
namespace PyTritonOptions {
  /* Execution configurations */
  char              *startAnalysisFromSymbol = nullptr;
  std::set<__uint>  startAnalysisFromAddr;
  std::set<__uint>  startAnalysisFromOffset;
  std::set<__uint>  stopAnalysisFromAddr;
  std::set<__uint>  stopAnalysisFromOffset;

  /* Callback configurations */
  PyObject *callbackAfter         = nullptr;                // After the instruction processing
  PyObject *callbackBefore        = nullptr;                // Before the instruction processing
  PyObject *callbackBeforeIRProc  = nullptr;                // Before the IR processing
  PyObject *callbackFini          = nullptr;                // At the end of the execution
  PyObject *callbackSignals       = nullptr;                // When a signal occurs
  PyObject *callbackSyscallEntry  = nullptr;                // Before syscall processing
  PyObject *callbackSyscallExit   = nullptr;                // After syscall processing
  PyObject *callbackImageLoad     = nullptr;                // When an image is loaded
  std::map<const char *, PyObject *> callbackRoutineEntry;  // Before routine processing
  std::map<const char *, PyObject *> callbackRoutineExit;   // After routine processing
  std::list<const char *>            imageWhitelist;        // An image white list
  std::list<const char *>            imageBlacklist;        // An image black list

  /* Taint configurations */
  std::map<__uint, std::list<__uint>> taintRegFromAddr;   // <addr, [reg1, reg2]>
  std::map<__uint, std::list<__uint>> untaintRegFromAddr; // <addr, [reg1, reg2]>
  std::map<__uint, std::list<__uint>> taintMemFromAddr;   // <addr, [mem1, mem2]>
  std::map<__uint, std::list<__uint>> untaintMemFromAddr; // <addr, [mem1, mem2]>
};


static char Triton_addCallback_doc[] = "Adds a callback for each instruction instrumented";
static PyObject *Triton_addCallback(PyObject *self, PyObject *args) {
  PyObject *function = nullptr;
  PyObject *flag = nullptr;
  PyObject *routine = nullptr;


  /* Extract arguments */
  PyArg_ParseTuple(args, "|OOO", &function, &flag, &routine);

  if (function == nullptr || !PyCallable_Check(function))
    return PyErr_Format(PyExc_TypeError, "addCallback(): expected a function callback as first argument");

  /* Check if the second arg is an IDREF.CALLBACK*/
  if (flag == nullptr || (!PyLong_Check(flag) && !PyInt_Check(flag)))
    return PyErr_Format(PyExc_TypeError, "addCallback(): expected an IDREF.CALLBACK (integer) as second argument");

  if (PyLong_AsUint(flag) == CB_BEFORE)
    PyTritonOptions::callbackBefore = function;

  else if ((PyLong_AsUint(flag) == CB_BEFORE_SYMPROC))
    PyTritonOptions::callbackBeforeIRProc = function;

  else if ((PyLong_AsUint(flag) == CB_AFTER))
    PyTritonOptions::callbackAfter = function;

  else if ((PyLong_AsUint(flag) == CB_FINI))
    PyTritonOptions::callbackFini = function;

  else if ((PyLong_AsUint(flag) == CB_SIGNALS))
    PyTritonOptions::callbackSignals = function;

  else if ((PyLong_AsUint(flag) == CB_SYSCALL_ENTRY))
    PyTritonOptions::callbackSyscallEntry = function;

  else if ((PyLong_AsUint(flag) == CB_SYSCALL_EXIT))
    PyTritonOptions::callbackSyscallExit = function;

  else if (PyLong_AsUint(flag) == CB_IMAGE_LOAD)
    PyTritonOptions::callbackImageLoad = function;

  else if ((PyLong_AsUint(flag) == CB_ROUTINE_ENTRY)){
    if (routine == nullptr || !PyString_Check(routine))
      return PyErr_Format(PyExc_TypeError, "addCallback(): expected a routine name (string) as third argument");
    PyTritonOptions::callbackRoutineEntry.insert(std::pair<const char*,PyObject*>(PyString_AsString(routine), function));
  }

  else if ((PyLong_AsUint(flag) == CB_ROUTINE_EXIT)){
    if (routine == nullptr || !PyString_Check(routine))
      return PyErr_Format(PyExc_TypeError, "addCallback(): expected a routine name (string) as third argument");
    PyTritonOptions::callbackRoutineExit.insert(std::pair<const char*,PyObject*>(PyString_AsString(routine), function));
  }

  else
    return PyErr_Format(PyExc_TypeError, "addCallback(): expected an IDREF.CALLBACK (integer) as second argument");

  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_checkReadAccess_doc[] = "Checks whether the memory page which contains this address has a read access protection";
static PyObject *Triton_checkReadAccess(PyObject *self, PyObject *addr) {
  __uint ad;

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "checkReadAccess(): expected an address (integer) as argument");

  ad = PyLong_AsUint(addr);
  if (PIN_CheckReadAccess(reinterpret_cast<void*>(ad)) == true)
    Py_RETURN_TRUE;

  Py_RETURN_FALSE;
}


static char Triton_checkWriteAccess_doc[] = "Checks whether the memory page which contains this address has a write access protection";
static PyObject *Triton_checkWriteAccess(PyObject *self, PyObject *addr) {
  __uint ad;

  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "checkWriteAccess(): expected an address (integer) as argument");

  ad = PyLong_AsUint(addr);
  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(ad)) == true)
    Py_RETURN_TRUE;

  Py_RETURN_FALSE;
}


static char Triton_detachProcess_doc[] = "Detach from the targeted process";
static PyObject *Triton_detachProcess(PyObject *self, PyObject *noarg) {
  PIN_Detach();
  analysisTrigger.update(false);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_getMemValue_doc[] = "Gets the current value of the memory";
static PyObject *Triton_getMemValue(PyObject *self, PyObject *args) {
  PyObject *addr = nullptr;
  PyObject *readSize = nullptr;
  __uint ad;
  __uint rs;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &addr, &readSize);

  if (!ap.getCurrentCtxH())
    return PyErr_Format(PyExc_TypeError, "getMemValue(): Can't call getMemValue() right now. You must run the program before.");

  if (addr == nullptr || (!PyLong_Check(addr) && !PyInt_Check(addr)))
    return PyErr_Format(PyExc_TypeError, "getMemValue(): expected an address (integer) as first argument");

  if (readSize == nullptr || (!PyLong_Check(readSize) && !PyInt_Check(readSize)))
    return PyErr_Format(PyExc_TypeError, "getMemValue(): expected a read size (integer) as second argument");

  ad = PyLong_AsUint(addr);
  rs = PyLong_AsUint(readSize);

  if (rs == 0)
    return PyErr_Format(PyExc_TypeError, "getMemValue(): The readSize cannot be 0");

  if (rs > DQWORD_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "getMemValue(): The readSize must be less than 128");

  if (rs % BYTE_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "getMemValue(): The readSize must be a multiple of 8");

  if (PIN_CheckReadAccess(reinterpret_cast<void*>(ad)) == false)
    return PyErr_Format(PyExc_TypeError, "getMemValue(): The targeted address memory can not be read");

  rs = rs / BYTE_SIZE_BIT;
  MemoryOperand mem(ad, rs);

  /* If this is a 128-bits read size, we must use uint128ToPyLongObject() */
  uint128 value = ap.getMemValue(mem, rs);
  return uint128ToPyLongObject(value);
}


static char Triton_getRegName_doc[] = "Gets the register name";
static PyObject *Triton_getRegName(PyObject *self, PyObject *reg) {
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "getRegName(): expected a register id (integer) as argument");

  return Py_BuildValue("s", PINConverter::getRegisterName(PyLong_AsUint(reg)).c_str());
}


static char Triton_getRegValue_doc[] = "Gets the current value of the register";
static PyObject *Triton_getRegValue(PyObject *self, PyObject *regId) {
  RegisterOperand reg;
  __uint tritonReg;

  if (!PyLong_Check(regId) && !PyInt_Check(regId))
    return PyErr_Format(PyExc_TypeError, "getRegValue(): expected a register id (IDREF.REG) as argument");

  if (!ap.getCurrentCtxH())
    return PyErr_Format(PyExc_TypeError, "getRegValue(): Can't call getRegValue() right now. You must run the program before.");

  tritonReg = PyLong_AsUint(regId);
  reg = createTmpReg(tritonReg);

  if (isSSERegId(tritonReg)){
    uint128 value = ap.getSSERegisterValue(reg);
    return uint128ToPyLongObject(value);
  }

  return Py_BuildValue("k", ap.getRegisterValue(reg));
}


static char Triton_getFlagValue_doc[] = "Gets the current value of the flag";
static PyObject *Triton_getFlagValue(PyObject *self, PyObject *flagId) {
  RegisterOperand flag;

  if (!PyLong_Check(flagId) && !PyInt_Check(flagId))
    return PyErr_Format(PyExc_TypeError, "getFlagValue(): expected a flag id (IDREF.FLAG) as argument");

  if (!ap.getCurrentCtxH())
    return PyErr_Format(PyExc_TypeError, "getFlagValue(): Can't call getFlagValue() right now. You must run the program before.");

  flag = createTmpFlag(PyLong_AsUint(flagId));

  return Py_BuildValue("k", ap.getFlagValue(flag));
}


static char Triton_getSyscallArgument_doc[] = "Returns the syscall argument.";
static PyObject *Triton_getSyscallArgument(PyObject *self, PyObject *args) {
  PyObject *num = nullptr;
  PyObject *std = nullptr;
  __uint ret;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &std, &num);

  if (std == nullptr || (!PyLong_Check(std) && !PyInt_Check(std)))
    return PyErr_Format(PyExc_TypeError, "getSyscallArgument(): expected an id (integer) as first argument");

  if (num == nullptr || (!PyLong_Check(num) && !PyInt_Check(num)))
    return PyErr_Format(PyExc_TypeError, "getSyscallArgument(): expected an id (integer) as second argument");

  LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(PyLong_AsUint(std));;
  CONTEXT *ctx = static_cast<CONTEXT*>(ap.getCurrentCtxH()->getCtx());

  ret = PIN_GetSyscallArgument(ctx, standard, PyLong_AsUint(num));

  return PyLong_FromUint(ret);
}


static char Triton_getSyscallNumber_doc[] = "Returns the syscall number. This function must be called inside the syscall entry callback. Otherwise returns results in undefined behavior.";
static PyObject *Triton_getSyscallNumber(PyObject *self, PyObject *std) {
  __uint syscallNumber;

  if (!PyLong_Check(std) && !PyInt_Check(std))
    return PyErr_Format(PyExc_TypeError, "getSyscallNumber(): expected an id (integer) as argument");

  LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(PyLong_AsUint(std));;
  CONTEXT *ctx = static_cast<CONTEXT*>(ap.getCurrentCtxH()->getCtx());

  syscallNumber = PIN_GetSyscallNumber(ctx, standard);

  return PyLong_FromUint(syscallNumber);
}


static char Triton_getSyscallReturn_doc[] = "Returns the syscall return value.";
static PyObject *Triton_getSyscallReturn(PyObject *self, PyObject *std) {
  __uint ret;

  if (!PyLong_Check(std) && !PyInt_Check(std))
    return PyErr_Format(PyExc_TypeError, "getSyscallReturn(): expected an id (integer) as argument");

  LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(PyLong_AsUint(std));;
  CONTEXT *ctx = static_cast<CONTEXT*>(ap.getCurrentCtxH()->getCtx());

  ret = PIN_GetSyscallReturn(ctx, standard);

  return PyLong_FromUint(ret);
}


static char Triton_opcodeToString_doc[] = "Returns a string with the opcode of the instruction";
static PyObject *Triton_opcodeToString(PyObject *self, PyObject *opcode) {
  if (!PyLong_Check(opcode) && !PyInt_Check(opcode))
    return PyErr_Format(PyExc_TypeError, "opcodeToString(): expected an opcode (integer) as argument");

  return Py_BuildValue("s", OPCODE_StringShort(PyLong_AsUint(opcode)).c_str());
}


static char Triton_runProgram_doc[] = "Starts the Pin instrumentation";
static PyObject *Triton_runProgram(PyObject *self, PyObject *noarg) {
  /* Never returns - Rock 'n roll baby \o/ */
  PIN_StartProgram();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setATTSyntax_doc[] = "Sets the AT&T syntax";
static PyObject *Triton_setATTSyntax(PyObject *self, PyObject *noarg) {
  PIN_SetSyntaxATT();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setIntelSyntax_doc[] = "Sets the Intel syntax";
static PyObject *Triton_setIntelSyntax(PyObject *self, PyObject *noarg) {
  PIN_SetSyntaxIntel();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setXEDSyntax_doc[] = "Sets the XED syntax";
static PyObject *Triton_setXEDSyntax(PyObject *self, PyObject *noarg) {
  PIN_SetSyntaxXED();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setMemValue_doc[] = "Inserts value into the runtime memory";
static PyObject *Triton_setMemValue(PyObject *self, PyObject *args) {
  PyObject  *addr = nullptr;
  PyObject  *value = nullptr;
  PyObject  *writeSize = nullptr;
  uint128   va; // value
  __uint    ad; // address
  __uint    ws; // write size

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OOO", &addr, &writeSize, &value);

  if (addr == nullptr || (!PyLong_Check(addr) && !PyInt_Check(addr)))
    return PyErr_Format(PyExc_TypeError, "setMemValue(): expected an address (integer) as first argument");

  if (writeSize == nullptr || (!PyLong_Check(writeSize) && !PyInt_Check(writeSize)))
    return PyErr_Format(PyExc_TypeError, "setMemValue(): expected an integer as second argument");

  if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
    return PyErr_Format(PyExc_TypeError, "setMemValue(): expected an integer as third argument");

  ad = PyLong_AsUint(addr);
  ws = PyLong_AsUint(writeSize);

  if (ws == 0)
    return PyErr_Format(PyExc_TypeError, "setMemValue(): The writeSize cannot be 0");

  if (ws > DQWORD_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "setMemValue(): The writeSize must be less than 128");

  if (ws % BYTE_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "setMemValue(): The writeSize must be a multiple of 8");

  if (PIN_CheckWriteAccess(reinterpret_cast<void*>(ad)) == false)
    return PyErr_Format(PyExc_TypeError, "setMemValue(): Can not write into the targeted address memory");

  va = PyLongObjectToUint128(value);
  ws = ws / BYTE_SIZE_BIT;
  MemoryOperand mo(ad, ws);
  ap.setMemValue(mo, ws, va);

  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setRegValue_doc[] = "Inserts value into the current context register";
static PyObject *Triton_setRegValue(PyObject *self, PyObject *args) {
  PyObject *reg = nullptr;
  PyObject *value = nullptr;
  uint128  va;
  __uint   tr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &reg, &value);

  if (reg == nullptr || (!PyLong_Check(reg) && !PyInt_Check(reg)))
    return PyErr_Format(PyExc_TypeError, "setRegValue(): expected an IDREF.REG as first argument");

  if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
    return PyErr_Format(PyExc_TypeError, "setRegValue(): expected an integer as second argument");

  va = PyLongObjectToUint128(value);
  tr = PyLong_AsUint(reg);
  RegisterOperand ro = createTmpReg(tr);

  if (isSSERegId(tr))
    ap.setSSERegisterValue(ro, va);
  else
    ap.setRegisterValue(ro, boost::numeric_cast<__uint>(va));

  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setupImageBlacklist_doc[] = "Setup an image blacklist";
static PyObject *Triton_setupImageBlacklist(PyObject *self, PyObject *arg) {

  /* Check if the arg is a list */
  if (!PyList_Check(arg))
    return PyErr_Format(PyExc_TypeError, "setupImageBlacklist(): expected a list as first argument");

  /* Check if the arg list contains only string item and insert them in the internal list */
  for (Py_ssize_t i = 0; i < PyList_Size(arg); i++){
    PyObject *item = PyList_GetItem(arg, i);

    if (!PyString_Check(item))
      return PyErr_Format(PyExc_TypeError, "setupImageBlacklist(): The first argument must be a list of image name (string)");

    PyTritonOptions::imageBlacklist.push_back(PyString_AsString(item));
  }

  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_setupImageWhitelist_doc[] = "Setup an image whitelist";
static PyObject *Triton_setupImageWhitelist(PyObject *self, PyObject *arg) {

  /* Check if the arg is a list */
  if (!PyList_Check(arg))
    return PyErr_Format(PyExc_TypeError, "setupImageWhitelist(): expected a list as first argument");

  /* Check if the arg list contains only string item and insert them in the internal list */
  for (Py_ssize_t i = 0; i < PyList_Size(arg); i++){
    PyObject *item = PyList_GetItem(arg, i);

    if (!PyString_Check(item))
      return PyErr_Format(PyExc_TypeError, "setupImageWhitelist(): The first argument must be a list of image name (string)");

    PyTritonOptions::imageWhitelist.push_back(PyString_AsString(item));
  }

  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_startAnalysisFromSymbol_doc[] = "Starts the symbolic execution from a specific name point";
static PyObject *Triton_startAnalysisFromSymbol(PyObject *self, PyObject *name) {

  if (!PyString_Check(name))
    return PyErr_Format(PyExc_TypeError, "startAnalysisFromSymbol(): expected a string as argument");

  PyTritonOptions::startAnalysisFromSymbol = PyString_AsString(name);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_startAnalysisFromAddr_doc[] = "Starts the symbolic execution from a specific address";
static PyObject *Triton_startAnalysisFromAddr(PyObject *self, PyObject *addr) {
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "startAnalysisFromAddr(): expected an address (integer) as argument");

  PyTritonOptions::startAnalysisFromAddr.insert(PyLong_AsUint(addr));
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_startAnalysisFromOffset_doc[] = "Starts the symbolic execution from a specific offset in the binary";
static PyObject *Triton_startAnalysisFromOffset(PyObject *self, PyObject *offset) {
  if (!PyLong_Check(offset) && !PyInt_Check(offset))
    return PyErr_Format(PyExc_TypeError, "startAnalysisFromOffset(): expected an offset (integer) as argument");

  PyTritonOptions::startAnalysisFromOffset.insert(PyLong_AsUint(offset));
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_stopAnalysisFromAddr_doc[] = "Stops the symbolic execution from a specific address";
static PyObject *Triton_stopAnalysisFromAddr(PyObject *self, PyObject *addr) {
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "stopAnalysisFromAddr(): expected an address (integer) as argument");

  PyTritonOptions::stopAnalysisFromAddr.insert(PyLong_AsUint(addr));
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_stopAnalysisFromOffset_doc[] = "Stops the symbolic execution from a specific offset in the binary";
static PyObject *Triton_stopAnalysisFromOffset(PyObject *self, PyObject *offset) {
  if (!PyLong_Check(offset) && !PyInt_Check(offset))
    return PyErr_Format(PyExc_TypeError, "stopAnalysisFromOffset(): expected an offset (integer) as argument");

  PyTritonOptions::stopAnalysisFromOffset.insert(PyLong_AsUint(offset));
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_syscallToString_doc[] = "Returns the syscall string from a syscall number";
static PyObject *Triton_syscallToString(PyObject *self, PyObject *args) {
  PyObject *std = nullptr;
  PyObject *num = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &std, &num);

  if (std == nullptr || (!PyLong_Check(std) && !PyInt_Check(std)))
    return PyErr_Format(PyExc_TypeError, "syscallToString(): expected a standard IDREF.SYSCALL as first argument");

  if (num == nullptr || (!PyLong_Check(num) && !PyInt_Check(num)))
    return PyErr_Format(PyExc_TypeError, "syscallToString(): expected a syscall number (integer) as second argument");

  const char *syscall = nullptr;
  switch (PyLong_AsUint(std)){
    case SYSCALL_STANDARD_IA32_LINUX:
    case SYSCALL_STANDARD_IA32E_LINUX:
      syscall = syscallNumberLinuxToString(PyLong_AsUint(num));
      break;
    default:
      return PyErr_Format(PyExc_TypeError, "syscallToString(): IDREF.SYSCALL standard unsupported");
  }

  if (syscall == nullptr)
    return PyErr_Format(PyExc_TypeError, "syscallToString(): IDREF.SYSCALL number unsupported");

  return Py_BuildValue("s", syscall);
}

#ifndef LIGHT_VERSION

static char Triton_concretizeAllMem_doc[] = "Concretize all memory reference";
static PyObject *Triton_concretizeAllMem(PyObject *self, PyObject *noarg) {
  ap.concretizeAllMem();
  Py_RETURN_TRUE;
}


static char Triton_assignSymExprToReg_doc[] = "Assign a symbolic expression to a register";
static PyObject *Triton_assignSymExprToReg(PyObject *self, PyObject *args) {
  PyObject *expr  = nullptr;
  PyObject *regId = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &expr, &regId);

  if (expr == nullptr || !PySymbolicExpression_Check(expr))
    return PyErr_Format(PyExc_TypeError, "assignSymExprToReg(): expected a SymbolicExpression as first argument");

  if (regId == nullptr || (!PyLong_Check(regId) && !PyInt_Check(regId)))
    return PyErr_Format(PyExc_TypeError, "assignSymExprToReg(): expected a register id (IDREF.REG) as second argument");

  if (ap.assignSEToReg(PySymbolicExpression_AsSymbolicExpression(expr), PyLong_AsUint(regId)) == false)
    return PyErr_Format(PyExc_TypeError, "assignSymExprToReg(): Invalid register id");

  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_concretizeAllReg_doc[] = "Concretize all registers reference";
static PyObject *Triton_concretizeAllReg(PyObject *self, PyObject *noarg) {
  ap.concretizeAllReg();
  Py_RETURN_TRUE;
}


static char Triton_concretizeMem_doc[] = "Concretize a memory reference";
static PyObject *Triton_concretizeMem(PyObject *self, PyObject *addr) {
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "concretizeMem(): expected an address (integer) as argument");

  MemoryOperand mem(PyLong_AsUint(addr), 1);
  ap.concretizeMem(mem);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_concretizeReg_doc[] = "Concretize a register reference";
static PyObject *Triton_concretizeReg(PyObject *self, PyObject *regId) {
  if (!PyLong_Check(regId) && !PyInt_Check(regId))
    return PyErr_Format(PyExc_TypeError, "concretizeReg(): expected a IDREF.REG as argument");

  RegisterOperand reg = createTmpReg(PyLong_AsUint(regId));
  ap.concretizeReg(reg);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_convertExprToSymVar_doc[] = "Converts an expression to a symbolic variable";
static PyObject *Triton_convertExprToSymVar(PyObject *self, PyObject *args) {
  PyObject *exprId = nullptr;
  PyObject *symVarSize = nullptr;
  PyObject *varComment = nullptr;
  __uint vs, ei;
  std::string vc;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OOO", &exprId, &symVarSize, &varComment);

  if (varComment == nullptr)
    varComment = PyString_FromString("");

  if (exprId == nullptr || (!PyLong_Check(exprId) && !PyInt_Check(exprId)))
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected an integer as first argument");

  if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected an integer as second argument");

  if (PyLong_AsUint(symVarSize) == 0)
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): The size must cannot be 0");

  if (PyLong_AsUint(symVarSize) % BYTE_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): The size must be a multiple of 8");

  if (PyLong_AsUint(symVarSize) > DQWORD_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): The size must be less than 128");

  if (!PyString_Check(varComment))
      return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): expected a comment (string) as third argument");

  ei = PyLong_AsUint(exprId);
  vs = PyLong_AsUint(symVarSize);
  vc = PyString_AsString(varComment);

  return PySymbolicVariable(ap.convertExprToSymVar(ei, vs, vc));
}


static char Triton_convertMemToSymVar_doc[] = "Converts a memory address to a symbolic variable";
static PyObject *Triton_convertMemToSymVar(PyObject *self, PyObject *args) {
  PyObject *memAddr = nullptr;
  PyObject *symVarSize = nullptr;
  PyObject *varComment = nullptr;
  __uint vs;
  std::string vc;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OOO", &memAddr, &symVarSize, &varComment);

  if (varComment == nullptr)
    varComment = PyString_FromString("");

  if (memAddr == nullptr || (!PyLong_Check(memAddr) && !PyInt_Check(memAddr)))
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): expected a memory address as first argument");

  if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): expected a size as second argument");

  if (PyLong_AsUint(symVarSize) == 0)
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): The size must cannot be 0");

  if (PyLong_AsUint(symVarSize) % BYTE_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): The size must be a multiple of 8");

  if (PyLong_AsUint(symVarSize) > DQWORD_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): The size must be less than 128");

  if (!PyString_Check(varComment))
      return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): expected a comment (string) as third argument");

  vs = PyLong_AsUint(symVarSize) / BYTE_SIZE_BIT;
  vc = PyString_AsString(varComment);
  MemoryOperand mo(PyLong_AsUint(memAddr), vs);

  return PySymbolicVariable(ap.convertMemToSymVar(mo, vs, vc));
}


static char Triton_convertRegToSymVar_doc[] = "Converts a register to a symbolic variable";
static PyObject *Triton_convertRegToSymVar(PyObject *self, PyObject *args) {
  PyObject *regId = nullptr;
  PyObject *symVarSize = nullptr;
  PyObject *varComment = nullptr;
  __uint vs;
  std::string vc;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OOO", &regId, &symVarSize, &varComment);

  if (varComment == nullptr)
    varComment = PyString_FromString("");

  if (regId == nullptr || (!PyLong_Check(regId) && !PyInt_Check(regId)))
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): expected a IDREF.REG as first argument");

  if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): expected a size as second argument");

  if (PyLong_AsUint(symVarSize) == 0)
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): The size must cannot be 0");

  if (PyLong_AsUint(symVarSize) % BYTE_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): The size must be a multiple of 8");

  if (PyLong_AsUint(symVarSize) > DQWORD_SIZE_BIT)
    return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): The size must be less than 128");

  if (!PyString_Check(varComment))
      return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): expected a comment (string) as third argument");

  vs = PyLong_AsUint(symVarSize);
  vc = PyString_AsString(varComment);
  RegisterOperand ro = createTmpReg(PyLong_AsUint(regId));

  return PySymbolicVariable(ap.convertRegToSymVar(ro, vs, vc));
}


static char Triton_createSymExpr_doc[] = "Create a new symbolic expression";
static PyObject *Triton_createSymExpr(PyObject *self, PyObject *args) {
  SymbolicExpression *se = nullptr;
  PyObject *symExpr = nullptr;
  PyObject *symComment = nullptr;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &symExpr, &symComment);

  if (symComment == nullptr)
    symComment = PyString_FromString("");

  if (symExpr == nullptr || !PySmtAstNode_Check(symExpr))
    return PyErr_Format(PyExc_TypeError, "createSymExpr(): expected a SmtAstNode as first argument");

  if (!PyString_Check(symComment))
      return PyErr_Format(PyExc_TypeError, "createSymExpr(): expected a comment (string) as second argument");

  se = ap.createSE(PySmtAstNode_AsSmtAstNode(symExpr), PyString_AsString(symComment));
  if (se == nullptr)
    return PyErr_Format(PyExc_TypeError, "createSymExpr(): Cannot create the symbolic expression");

  return PySymbolicExpression(se);
}


static char Triton_disableSnapshot_doc[] = "Disables the snapshot engine";
static PyObject *Triton_disableSnapshot(PyObject *self, PyObject *noarg) {
  ap.disableSnapshot();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_disableSymEngine_doc[] = "Disables the symbolic engine";
static PyObject *Triton_disableSymEngine(PyObject *self, PyObject *noarg) {
  ap.disableSymEngine();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_enableSymEngine_doc[] = "Enables the symbolic engine";
static PyObject *Triton_enableSymEngine(PyObject *self, PyObject *noarg) {
  ap.enableSymEngine();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_evaluateAST_doc[] = "Evaluate an AST";
static PyObject *Triton_evaluateAST(PyObject *self, PyObject *smtAST) {
  uint512 value = 0;

  if (!PySmtAstNode_Check(smtAST))
    return PyErr_Format(PyExc_TypeError, "evaluateAST(): expected an SmtAstNode as argument");

  value = ap.evaluateAST(PySmtAstNode_AsSmtAstNode(smtAST));

  return uint512ToPyLongObject(value);
}


static char Triton_getFullExpression_doc[] = "Returns the full symbolic expression backtracked";
static PyObject *Triton_getFullExpression(PyObject *self, PyObject *node) {
  smt2lib::smtAstAbstractNode *fullExpr;

  if (!PySmtAstNode_Check(node))
    return PyErr_Format(PyExc_TypeError, "getFullSymExpr(): expected an SmtAstNode node as argument");

  fullExpr = ap.getFullExpression(PySmtAstNode_AsSmtAstNode(node));
  if (fullExpr == nullptr) {
    Py_INCREF(Py_None);
    return Py_None;
  }

  return PySmtAstNode(fullExpr);
}


static char Triton_getMemSymbolicID_doc[] = "Gets the symbolic memory reference";
static PyObject *Triton_getMemSymbolicID(PyObject *self, PyObject *addr) {
  if (!PyLong_Check(addr) && !PyInt_Check(addr))
    return PyErr_Format(PyExc_TypeError, "getMemSymbolicID(): expected a memory address (integer) as argument");

  MemoryOperand mem(PyLong_AsUint(addr), 1);
  return Py_BuildValue("k", ap.getMemSymbolicID(mem));
}


static char Triton_getModel_doc[] = "Returns a model of the symbolic expression";
static PyObject *Triton_getModel(PyObject *self, PyObject *node) {
  std::list<Smodel>::iterator it;
  std::list<Smodel> model;

  if (!PySmtAstNode_Check(node))
    return PyErr_Format(PyExc_TypeError, "getModel(): expected a SmtAstNode as argument");

  /* Get model */
  model = ap.getModel(PySmtAstNode_AsSmtAstNode(node));

  /* Craft the model dictionary */
  PyObject *modelDict = xPyDict_New();
  for (it = model.begin() ; it != model.end(); it++)
    PyDict_SetItemString(modelDict, it->getName().c_str(), Py_BuildValue("k", it->getValue()));

  return modelDict;
}


static char Triton_getModels_doc[] = "Returns all models of the symbolic expression";
static PyObject *Triton_getModels(PyObject *self, PyObject *args) {
  PyObject                        *limit = nullptr;
  PyObject                        *modelsList;
  PyObject                        *node = nullptr;
  std::vector<std::list<Smodel>>  models;
  __uint                          limit_c = 0;
  __uint                          modelsSize = 0;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &node, &limit);

  if (node == nullptr || !PySmtAstNode_Check(node))
    return PyErr_Format(PyExc_TypeError, "getModels(): expected a SmtAstNode as first argument");

  if (limit == nullptr || (!PyLong_Check(limit) && !PyInt_Check(limit)))
    return PyErr_Format(PyExc_TypeError, "getModels(): expected a limit (integer) as second argument");

  limit_c = PyLong_AsUint(limit);
  if (limit_c == 0)
    return PyErr_Format(PyExc_TypeError, "getModels(): The limit must be greater than 0");

  /* Get models */
  models        = ap.getModels(PySmtAstNode_AsSmtAstNode(node), limit_c);
  modelsSize    = models.size();
  modelsList    = xPyList_New(modelsSize);

  for (__uint index = 0; index < modelsSize; index++){
    std::list<Smodel> model = models[index];
    std::list<Smodel>::iterator it;
    /* Craft the model dictionary */
    PyObject *modelDict = xPyDict_New();
    for (it = model.begin() ; it != model.end(); it++)
      PyDict_SetItemString(modelDict, it->getName().c_str(), Py_BuildValue("k", it->getValue()));

    PyList_SetItem(modelsList, index, modelDict);
  }

  return modelsList;
}


static char Triton_getPathConstraints_doc[] = "Returns the list of path constraints";
static PyObject *Triton_getPathConstraints(PyObject *self, PyObject *noargs) {
  PyObject                        *ppc;
  std::list<__uint>               pc;
  std::list<__uint>::iterator     it;
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


static char Triton_getRegSymbolicID_doc[] = "Gets the symbolic register reference";
static PyObject *Triton_getRegSymbolicID(PyObject *self, PyObject *reg) {
  RegisterOperand ro;
  __uint regId = 0;

  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "getRegSymbolicID(): expected a register id (integer) as argument");

  regId = PyLong_AsUint(reg);
  ro = createTmpReg(regId);

  return Py_BuildValue("k", ap.getRegSymbolicID(ro));
}


static char Triton_getRegs_doc[] = "Returns informations about all registers";
static PyObject *Triton_getRegs(PyObject *self, PyObject *noargs) {
  PyObject *regs = xPyDict_New();

  /* Build all Registers */
  /* TODO_32Bits: something more sexy */
  #if defined(__x86_64__) || defined(_M_X64)
  for (__uint regId = ID_RAX; regId < ID_RFLAGS; regId++){
  #endif
  #if defined(__i386) || defined(_M_IX86)
  for (__uint regId = ID_EAX; regId < ID_EFLAGS; regId++){
  #endif
    PyObject *reg = xPyDict_New();
    RegisterOperand ro = createTmpReg(regId);
    if (isSSERegId(regId))
      PyDict_SetItemString(reg, "concreteValue", uint128ToPyLongObject(ap.getSSERegisterValue(ro)));
    else
      PyDict_SetItemString(reg, "concreteValue", Py_BuildValue("k", ap.getRegisterValue(ro)));
    PyDict_SetItemString(reg, "symbolicExpr", Py_BuildValue("k", ap.getRegSymbolicID(ro)));
    PyDict_SetItem(regs, Py_BuildValue("k", regId), reg);
  }

  /* Build all Flags */
  for (__uint flagId = ID_AF; flagId <= ID_ZF; flagId++){
    PyObject *flag = xPyDict_New();
    RegisterOperand fo = createTmpFlag(flagId);
    PyDict_SetItemString(flag, "concreteValue", Py_BuildValue("k", ap.getFlagValue(fo)));
    PyDict_SetItemString(flag, "symbolicExpr", Py_BuildValue("k", ap.getRegSymbolicID(fo)));
    PyDict_SetItem(regs, Py_BuildValue("k", flagId), flag);
  }

  return regs;
}


static char Triton_getStats_doc[] = "Returns statistics of the execution";
static PyObject *Triton_getStats(PyObject *self, PyObject *noargs) {
  PyObject *stats = xPyDict_New();
  PyDict_SetItemString(stats, "branches",     PyLong_FromUint(ap.getNumberOfBranchesTaken()));
  PyDict_SetItemString(stats, "expressions",  PyLong_FromUint(ap.getNumberOfExpressions()));
  PyDict_SetItemString(stats, "time",         PyLong_FromUint(ap.getTimeOfExecution()));
  PyDict_SetItemString(stats, "unknownExpr",  PyLong_FromUint(ap.getNumberOfUnknownInstruction()));
  return stats;
}


static char Triton_getSymExpr_doc[] = "Returns a SymbolicExpression class corresponding to the symbolic expression ID.";
static PyObject *Triton_getSymExpr(PyObject *self, PyObject *id) {
  __uint              exprId;
  SymbolicExpression  *expr;

  if (!PyLong_Check(id) && !PyInt_Check(id))
    return PyErr_Format(PyExc_TypeError, "getSymExpr(): expected an id (integer) as argument");

  exprId = PyLong_AsUint(id);
  expr = ap.getExpressionFromId(exprId);

  if (expr == nullptr)
    return PyErr_Format(PyExc_TypeError, "getSymExpr(): Invalid symbolic expression ID");

  return PySymbolicExpression(expr);
}


static char Triton_getSymExprs_doc[] = "Returns all SymbolicExpression class.";
static PyObject *Triton_getSymExprs(PyObject *self, PyObject *noargs) {
  PyObject                          *ret;
  std::vector<SymbolicExpression *> exprs;
  __uint                            numberOfExprs = 0;

  exprs = ap.getExpressions();
  numberOfExprs = exprs.size();
  ret = xPyList_New(numberOfExprs);
  for (__uint index = 0; index < numberOfExprs; index++)
    PyList_SetItem(ret, index, PySymbolicExpression(exprs[index]));

  return ret;
}


static char Triton_getSymVar_doc[] = "Returns the symbolic variable class";
static PyObject *Triton_getSymVar(PyObject *self, PyObject *symVarPy) {
  SymbolicVariable *symVar;

  if (!PyLong_Check(symVarPy) && !PyInt_Check(symVarPy) && !PyString_Check(symVarPy))
    return PyErr_Format(PyExc_TypeError, "getSymVar(): expected a symbolic variable ID or a symbolic variable name");

  if (PyLong_Check(symVarPy) || PyInt_Check(symVarPy))
    symVar = ap.getSymVar(PyLong_AsUint(symVarPy));
  else
    symVar = ap.getSymVar(PyString_AsString(symVarPy));

  if (symVar == nullptr)
    return PyErr_Format(PyExc_TypeError, "getSymVar(): Invalid symbolic variable ID");

  return PySymbolicVariable(symVar);
}


static char Triton_getSymVarSize_doc[] = "Returns the size of the symbolic variable";
static PyObject *Triton_getSymVarSize(PyObject *self, PyObject *symVarPy) {
  SymbolicVariable *symVar;

  if (!PyLong_Check(symVarPy) && !PyInt_Check(symVarPy) && !PyString_Check(symVarPy))
    return PyErr_Format(PyExc_TypeError, "getSymVarSize(): expected a symbolic variable ID or a symbolic variable name");

  if (PyLong_Check(symVarPy) || PyInt_Check(symVarPy))
    symVar = ap.getSymVar(PyLong_AsUint(symVarPy));
  else
    symVar = ap.getSymVar(PyString_AsString(symVarPy));

  if (symVar == nullptr)
    return PyErr_Format(PyExc_TypeError, "getSymVarSize(): Invalid symbolic variable ID");

  return Py_BuildValue("k", symVar->getSymVarSize());
}


static char Triton_getSymVars_doc[] = "Returns the list of symbolic variables";
static PyObject *Triton_getSymVars(PyObject *self, PyObject *noArg) {
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


static char Triton_getTaintedExpressions_doc[] = "Returns a list which contains all tainted symbolic expressions";
static PyObject *Triton_getTaintedExpressions(PyObject *self, PyObject *noarg) {
  PyObject                                  *ret;
  std::list<SymbolicExpression *>           exprs;
  std::list<SymbolicExpression *>::iterator it;
  __uint                                    index = 0;
  __uint                                    numberOfExprs = 0;

  exprs = ap.getTaintedExpressions();
  numberOfExprs = exprs.size();
  ret = xPyList_New(numberOfExprs);
  for (it = exprs.begin(); it != exprs.end(); it++) {
    PyList_SetItem(ret, index, PySymbolicExpression(*it));
    index++;
  }

  return ret;
}


static char Triton_isMemTainted_doc[] = "Checks if the memory is tainted";
static PyObject *Triton_isMemTainted(PyObject *self, PyObject *mem) {
  if (!PyLong_Check(mem) && !PyInt_Check(mem))
    return PyErr_Format(PyExc_TypeError, "isMemTainted(): expected an address (integer) as argument");

  MemoryOperand mo(PyLong_AsUint(mem), 1);
  if (ap.isMemTainted(mo) == true)
    Py_RETURN_TRUE;

  Py_RETURN_FALSE;
}


static char Triton_isRegTainted_doc[] = "Checks if the register is tainted";
static PyObject *Triton_isRegTainted(PyObject *self, PyObject *reg) {
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "isRegTainted(): expected a register id (integer) as argument");

  RegisterOperand ro = createTmpReg(PyLong_AsUint(reg));
  if (ap.isRegTainted(ro) == true)
    Py_RETURN_TRUE;

  Py_RETURN_FALSE;
}


static char Triton_isSnapshotEnabled_doc[] = "Returns true if the snapshot is enabled";
static PyObject *Triton_isSnapshotEnabled(PyObject *self, PyObject *noarg) {
  if (ap.isSnapshotEnabled() == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static char Triton_isSymEngineEnabled_doc[] = "Returns true if the symbolic engine is enabled";
static PyObject *Triton_isSymEngineEnabled(PyObject *self, PyObject *noarg) {
  if (ap.isSymEngineEnabled() == true)
    Py_RETURN_TRUE;
  Py_RETURN_FALSE;
}


static char Triton_restoreSnapshot_doc[] = "Restores the last snapshot";
static PyObject *Triton_restoreSnapshot(PyObject *self, PyObject *noarg) {
  ap.setSnapshotRestoreFlag(true);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_taintMem_doc[] = "Taints an address memory";
static PyObject *Triton_taintMem(PyObject *self, PyObject *mem) {
  if (!PyLong_Check(mem) && !PyInt_Check(mem))
    return PyErr_Format(PyExc_TypeError, "TaintMem(): expected a memory address (integer) as argument");

  MemoryOperand mo(PyLong_AsUnsignedLong(mem), 1);
  ap.taintMem(mo);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_taintMemFromAddr_doc[] = "Taints specific memory address from an address";
static PyObject *Triton_taintMemFromAddr(PyObject *self, PyObject *args) {
  PyObject *addr = nullptr;
  PyObject *mems = nullptr;
  std::list<__uint> memsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &addr, &mems);

  /* Check if the first arg (addr) is a integer */
  if (addr == nullptr || (!PyLong_Check(addr) && !PyInt_Check(addr)))
    return PyErr_Format(PyExc_TypeError, "taintMemFromAddr(): expected an address as first argument");

  /* Check if the second arg (mems) is a list */
  if (mems == nullptr || !PyList_Check(mems))
    return PyErr_Format(PyExc_TypeError, "taintMemFromAddr(): expected a list as second argument");

  /* Check if the mems list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(mems); i++){
    PyObject *item = PyList_GetItem(mems, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "taintMemFromAddr(): The second argument must be a list of addresses (integer)");

    memsList.push_back(PyLong_AsUint(item));
  }

  /* Update taint configuration */
  PyTritonOptions::taintMemFromAddr.insert(std::pair<__uint, std::list<__uint>>(PyLong_AsUint(addr), memsList));
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_taintReg_doc[] = "Taints a register";
static PyObject *Triton_taintReg(PyObject *self, PyObject *reg) {
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "taintReg(): expected a register id (integer) as argument");

  RegisterOperand ro = createTmpReg(PyLong_AsUint(reg));
  ap.taintReg(ro);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_taintRegFromAddr_doc[] = "Taints specific registers from an address";
static PyObject *Triton_taintRegFromAddr(PyObject *self, PyObject *args) {
  PyObject *addr = nullptr;
  PyObject *regs = nullptr;
  std::list<__uint> regsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &addr, &regs);

  /* Check if the first arg (addr) is a integer */
  if (addr == nullptr || (!PyLong_Check(addr) && !PyInt_Check(addr)))
    return PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): expected an address as first argument");

  /* Check if the second arg (regs) is a list */
  if (regs == nullptr || !PyList_Check(regs))
    return PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): expected a list as second argument");

  /* Check if the regs list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(regs); i++){
    PyObject *item = PyList_GetItem(regs, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "taintRegFromAddr(): The second argument must be a list of register id (integer)");

    regsList.push_back(PyLong_AsUint(item));
  }

  /* Update taint configuration */
  PyTritonOptions::taintRegFromAddr.insert(std::pair<__uint, std::list<__uint>>(PyLong_AsUint(addr), regsList));
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_takeSnapshot_doc[] = "Takes a snapshot of the registers states and memory";
static PyObject *Triton_takeSnapshot(PyObject *self, PyObject *noarg) {
  ap.takeSnapshot();
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_untaintMem_doc[] = "Untaints an address memory";
static PyObject *Triton_untaintMem(PyObject *self, PyObject *mem) {
  if (!PyLong_Check(mem) && !PyInt_Check(mem))
    return PyErr_Format(PyExc_TypeError, "untaintMem(): expected a memory address (integer) as argument");

  MemoryOperand mo(PyLong_AsUint(mem), 1);
  ap.untaintMem(mo);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_untaintMemFromAddr_doc[] = "Untaints specific memory addresses from an address";
static PyObject *Triton_untaintMemFromAddr(PyObject *self, PyObject *args) {
  PyObject *addr = nullptr;
  PyObject *mems = nullptr;
  std::list<__uint> memsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &addr, &mems);

  /* Check if the first arg (addr) is a integer */
  if (addr == nullptr || (!PyLong_Check(addr) && !PyInt_Check(addr)))
    return PyErr_Format(PyExc_TypeError, "untaintMemFromAddr(): expected an address as first argument");

  /* Check if the second arg (mems) is a list */
  if (mems == nullptr || !PyList_Check(mems))
    return PyErr_Format(PyExc_TypeError, "untaintMemFromAddr(): expected a list as second argument");

  /* Check if the mems list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(mems); i++){
    PyObject *item = PyList_GetItem(mems, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "untaintMemFromAddr(): The second argument must be a list of register id (integer)");

    memsList.push_back(PyLong_AsUint(item));
  }

  /* Update taint configuration */
  PyTritonOptions::untaintMemFromAddr.insert(std::pair<__uint, std::list<__uint>>(PyLong_AsUint(addr), memsList));

  Py_INCREF(Py_None);
  return Py_None;
}



static char Triton_untaintReg_doc[] = "Untaints a register";
static PyObject *Triton_untaintReg(PyObject *self, PyObject *reg) {
  if (!PyLong_Check(reg) && !PyInt_Check(reg))
    return PyErr_Format(PyExc_TypeError, "untaintReg(): expected a register id (integer) as argument");

  RegisterOperand ro = createTmpReg(PyLong_AsUint(reg));
  ap.untaintReg(ro);
  Py_INCREF(Py_None);
  return Py_None;
}


static char Triton_untaintRegFromAddr_doc[] = "Untaints specific registers from an address";
static PyObject *Triton_untaintRegFromAddr(PyObject *self, PyObject *args) {
  PyObject *addr = nullptr;
  PyObject *regs = nullptr;
  std::list<__uint> regsList;

  /* Extract arguments */
  PyArg_ParseTuple(args, "|OO", &addr, &regs);

  /* Check if the first arg (addr) is a integer */
  if (addr == nullptr || (!PyLong_Check(addr) && !PyInt_Check(addr)))
    return PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): expected an address as first argument");

  /* Check if the second arg (regs) is a list */
  if (regs == nullptr || !PyList_Check(regs))
    return PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): expected a list as second argument");

  /* Check if the regs list contains only integer item and craft a std::list */
  for (Py_ssize_t i = 0; i < PyList_Size(regs); i++){
    PyObject *item = PyList_GetItem(regs, i);

    if (!PyLong_Check(item) && !PyInt_Check(item))
      return PyErr_Format(PyExc_TypeError, "untaintRegFromAddr(): The second argument must be a list of register id (integer)");

    regsList.push_back(PyLong_AsUint(item));
  }

  /* Update taint configuration */
  PyTritonOptions::untaintRegFromAddr.insert(std::pair<__uint, std::list<__uint>>(PyLong_AsUint(addr), regsList));

  Py_INCREF(Py_None);
  return Py_None;
}

#endif /* LIGHT_VERSION */


PyMethodDef tritonCallbacks[] = {
  {"addCallback",               Triton_addCallback,               METH_VARARGS, Triton_addCallback_doc},
  {"checkReadAccess",           Triton_checkReadAccess,           METH_O,       Triton_checkReadAccess_doc},
  {"checkWriteAccess",          Triton_checkWriteAccess,          METH_O,       Triton_checkWriteAccess_doc},
  {"detachProcess",             Triton_detachProcess,             METH_NOARGS,  Triton_detachProcess_doc},
  {"getFlagValue",              Triton_getFlagValue,              METH_O,       Triton_getFlagValue_doc},
  {"getMemValue",               Triton_getMemValue,               METH_VARARGS, Triton_getMemValue_doc},
  {"getRegName",                Triton_getRegName,                METH_O,       Triton_getRegName_doc},
  {"getRegValue",               Triton_getRegValue,               METH_O,       Triton_getRegValue_doc},
  {"getSyscallArgument",        Triton_getSyscallArgument,        METH_VARARGS, Triton_getSyscallArgument_doc},
  {"getSyscallNumber",          Triton_getSyscallNumber,          METH_O,       Triton_getSyscallNumber_doc},
  {"getSyscallReturn",          Triton_getSyscallReturn,          METH_O,       Triton_getSyscallReturn_doc},
  {"opcodeToString",            Triton_opcodeToString,            METH_O,       Triton_opcodeToString_doc},
  {"runProgram",                Triton_runProgram,                METH_NOARGS,  Triton_runProgram_doc},
  {"setATTSyntax",              Triton_setATTSyntax,              METH_NOARGS,  Triton_setATTSyntax_doc},
  {"setIntelSyntax",            Triton_setIntelSyntax,            METH_NOARGS,  Triton_setIntelSyntax_doc},
  {"setXEDSyntax",              Triton_setXEDSyntax,              METH_NOARGS,  Triton_setXEDSyntax_doc},
  {"setMemValue",               Triton_setMemValue,               METH_VARARGS, Triton_setMemValue_doc},
  {"setRegValue",               Triton_setRegValue,               METH_VARARGS, Triton_setRegValue_doc},
  {"setupImageBlacklist",       Triton_setupImageBlacklist,       METH_O,       Triton_setupImageBlacklist_doc},
  {"setupImageWhitelist",       Triton_setupImageWhitelist,       METH_O,       Triton_setupImageWhitelist_doc},
  {"startAnalysisFromAddr",     Triton_startAnalysisFromAddr,     METH_O,       Triton_startAnalysisFromAddr_doc},
  {"startAnalysisFromOffset",   Triton_startAnalysisFromOffset,   METH_O,       Triton_startAnalysisFromOffset_doc},
  {"startAnalysisFromSymbol",   Triton_startAnalysisFromSymbol,   METH_O,       Triton_startAnalysisFromSymbol_doc},
  {"stopAnalysisFromAddr",      Triton_stopAnalysisFromAddr,      METH_O,       Triton_stopAnalysisFromAddr_doc},
  {"stopAnalysisFromOffset",    Triton_stopAnalysisFromOffset,    METH_O,       Triton_stopAnalysisFromOffset_doc},
  {"syscallToString",           Triton_syscallToString,           METH_VARARGS, Triton_syscallToString_doc},
  #ifndef LIGHT_VERSION
  {"assignSymExprToReg",        Triton_assignSymExprToReg,        METH_VARARGS, Triton_assignSymExprToReg_doc},
  {"concretizeAllMem",          Triton_concretizeAllMem,          METH_NOARGS,  Triton_concretizeAllMem_doc},
  {"concretizeAllReg",          Triton_concretizeAllReg,          METH_NOARGS,  Triton_concretizeAllReg_doc},
  {"concretizeMem",             Triton_concretizeMem,             METH_O,       Triton_concretizeMem_doc},
  {"concretizeReg",             Triton_concretizeReg,             METH_O,       Triton_concretizeReg_doc},
  {"convertExprToSymVar",       Triton_convertExprToSymVar,       METH_VARARGS, Triton_convertExprToSymVar_doc},
  {"convertMemToSymVar",        Triton_convertMemToSymVar,        METH_VARARGS, Triton_convertMemToSymVar_doc},
  {"convertRegToSymVar",        Triton_convertRegToSymVar,        METH_VARARGS, Triton_convertRegToSymVar_doc},
  {"createSymExpr",             Triton_createSymExpr,             METH_VARARGS, Triton_createSymExpr_doc},
  {"disableSnapshot",           Triton_disableSnapshot,           METH_NOARGS,  Triton_disableSnapshot_doc},
  {"disableSymEngine",          Triton_disableSymEngine,          METH_NOARGS,  Triton_disableSymEngine_doc},
  {"enableSymEngine",           Triton_enableSymEngine,           METH_NOARGS,  Triton_enableSymEngine_doc},
  {"evaluateAST",               Triton_evaluateAST,               METH_O,       Triton_evaluateAST_doc},
  {"getFullExpression",         Triton_getFullExpression,         METH_O,       Triton_getFullExpression_doc},
  {"getMemSymbolicID",          Triton_getMemSymbolicID,          METH_O,       Triton_getMemSymbolicID_doc},
  {"getModel",                  Triton_getModel,                  METH_O,       Triton_getModel_doc},
  {"getModels",                 Triton_getModels,                 METH_VARARGS, Triton_getModels_doc},
  {"getPathConstraints",        Triton_getPathConstraints,        METH_NOARGS,  Triton_getPathConstraints_doc},
  {"getRegSymbolicID",          Triton_getRegSymbolicID,          METH_O,       Triton_getRegSymbolicID_doc},
  {"getRegs",                   Triton_getRegs,                   METH_NOARGS,  Triton_getRegs_doc},
  {"getStats",                  Triton_getStats,                  METH_NOARGS,  Triton_getStats_doc},
  {"getSymExpr",                Triton_getSymExpr,                METH_O,       Triton_getSymExpr_doc},
  {"getSymExprs",               Triton_getSymExprs,               METH_NOARGS,  Triton_getSymExprs_doc},
  {"getSymVar",                 Triton_getSymVar,                 METH_O,       Triton_getSymVar_doc},
  {"getSymVarSize",             Triton_getSymVarSize,             METH_O,       Triton_getSymVarSize_doc},
  {"getSymVars",                Triton_getSymVars,                METH_NOARGS,  Triton_getSymVars_doc},
  {"getTaintedExpressions",     Triton_getTaintedExpressions,     METH_NOARGS,  Triton_getTaintedExpressions_doc},
  {"isMemTainted",              Triton_isMemTainted,              METH_O,       Triton_isMemTainted_doc},
  {"isRegTainted",              Triton_isRegTainted,              METH_O,       Triton_isRegTainted_doc},
  {"isSnapshotEnabled",         Triton_isSnapshotEnabled,         METH_NOARGS,  Triton_isSnapshotEnabled_doc},
  {"isSymEngineEnabled",        Triton_isSymEngineEnabled,        METH_NOARGS,  Triton_isSymEngineEnabled_doc},
  {"restoreSnapshot",           Triton_restoreSnapshot,           METH_NOARGS,  Triton_restoreSnapshot_doc},
  {"taintMem",                  Triton_taintMem,                  METH_O,       Triton_taintMem_doc},
  {"taintMemFromAddr",          Triton_taintMemFromAddr,          METH_VARARGS, Triton_taintMemFromAddr_doc},
  {"taintReg",                  Triton_taintReg,                  METH_O,       Triton_taintReg_doc},
  {"taintRegFromAddr",          Triton_taintRegFromAddr,          METH_VARARGS, Triton_taintRegFromAddr_doc},
  {"takeSnapshot",              Triton_takeSnapshot,              METH_NOARGS,  Triton_takeSnapshot_doc},
  {"untaintMem",                Triton_untaintMem,                METH_O,       Triton_untaintMem_doc},
  {"untaintMemFromAddr",        Triton_untaintMemFromAddr,        METH_VARARGS, Triton_untaintMemFromAddr_doc},
  {"untaintReg",                Triton_untaintReg,                METH_O,       Triton_untaintReg_doc},
  {"untaintRegFromAddr",        Triton_untaintRegFromAddr,        METH_VARARGS, Triton_untaintRegFromAddr_doc},
  #endif
  {nullptr,                     nullptr,                          0,            nullptr}
};

