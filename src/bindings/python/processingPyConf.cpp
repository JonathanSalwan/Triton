/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <ProcessingPyConf.h>
#include <Registers.h>
#include <TritonPyObject.h>
#include <xPyFunc.h>



ProcessingPyConf::ProcessingPyConf(AnalysisProcessor *ap, Trigger *analysisTrigger) {
  this->ap = ap;
  this->analysisTrigger = analysisTrigger;
}


ProcessingPyConf::~ProcessingPyConf() {
}


void ProcessingPyConf::startAnalysisFromAddr(IRBuilder *irb) {
  // Check if the DSE must be start at this address
  if (PyTritonOptions::startAnalysisFromAddr.find(irb->getAddress()) != PyTritonOptions::startAnalysisFromAddr.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::startAnalysisFromOffset(IRBuilder *irb) {
  // Check if the DSE must be start at this offset
  if (PyTritonOptions::startAnalysisFromOffset.find(irb->getOffset()) != PyTritonOptions::startAnalysisFromOffset.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::stopAnalysisFromAddr(IRBuilder *irb) {
  // Check if the DSE must be stop at this address
  if (PyTritonOptions::stopAnalysisFromAddr.find(irb->getAddress()) != PyTritonOptions::stopAnalysisFromAddr.end())
    this->analysisTrigger->update(false);
}


void ProcessingPyConf::stopAnalysisFromOffset(IRBuilder *irb) {
  // Check if the DSE must be stop at this offset
  if (PyTritonOptions::stopAnalysisFromOffset.find(irb->getOffset()) != PyTritonOptions::stopAnalysisFromOffset.end())
    this->analysisTrigger->update(false);
}


#ifndef LIGHT_VERSION

void ProcessingPyConf::taintMemFromAddr(IRBuilder *irb) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is memory tainted via the python bindings
  std::list<uint64> memsTainted = PyTritonOptions::taintMemFromAddr[irb->getAddress()];
  std::list<uint64>::iterator it = memsTainted.begin();
  for ( ; it != memsTainted.end(); it++) {
    MemoryOperand mem(*it, 1);
    this->ap->taintMem(mem);
  }
}


void ProcessingPyConf::taintRegFromAddr(IRBuilder *irb) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers tainted via the python bindings
  std::list<uint64> regsTainted = PyTritonOptions::taintRegFromAddr[irb->getAddress()];
  std::list<uint64>::iterator it = regsTainted.begin();
  for ( ; it != regsTainted.end(); it++) {
    RegisterOperand reg = createTmpReg(*it);
    this->ap->taintReg(reg);
  }
}


void ProcessingPyConf::untaintMemFromAddr(IRBuilder *irb) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is memories untainted via the python bindings
  std::list<uint64> memsUntainted = PyTritonOptions::untaintMemFromAddr[irb->getAddress()];
  std::list<uint64>::iterator it = memsUntainted.begin();
  for ( ; it != memsUntainted.end(); it++) {
    MemoryOperand mem(*it, 1);
    this->ap->untaintMem(mem);
  }
}


void ProcessingPyConf::untaintRegFromAddr(IRBuilder *irb) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers untainted via the python bindings
  std::list<uint64> regsUntainted = PyTritonOptions::untaintRegFromAddr[irb->getAddress()];
  std::list<uint64>::iterator it = regsUntainted.begin();
  for ( ; it != regsUntainted.end(); it++) {
    RegisterOperand reg = createTmpReg(*it);
    this->ap->untaintReg(reg);
  }
}

#endif /* LIGHT_VERSION */

/*
 * When a callback is setup (triton.addCallback()), a class (Instruction) is
 * sent to the callback function as unique argument.
 */
void ProcessingPyConf::callbackAfter(Inst *inst, AnalysisProcessor *ap) {
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackAfter){

    /* Create the Instruction Python class */
    PyObject *instClass = PyInstruction(inst);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackAfter, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackBefore(Inst *inst, AnalysisProcessor *ap) {
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackBefore){

    /* Create the Instruction Python class */
    PyObject *instClass = PyInstruction(inst);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackBefore, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackBeforeIRProc(IRBuilder *irb, AnalysisProcessor *ap) {
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackBeforeIRProc){

    /* Create the Instruction Python class */
    PyObject *instClass = PyInstruction(irb);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackBeforeIRProc, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackFini(void) {
  // Check if there is a callback wich must be called at the end of the execution
  if (PyTritonOptions::callbackFini){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * There is no argument sent to the callback. */
    PyObject *args = xPyTuple_New(0);
    if (PyObject_CallObject(PyTritonOptions::callbackFini, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSignals(uint64 threadId, sint32 sig) {
  // Check if there is a callback wich must be called when a signal occurs
  if (PyTritonOptions::callbackSignals){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and sig are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromLong(threadId));
    PyTuple_SetItem(args, 1, Py_BuildValue("i", sig));
    if (PyObject_CallObject(PyTritonOptions::callbackSignals, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSyscallEntry(uint64 threadId, uint64 std) {
  // Check if there is a callback wich must be called before the syscall processing
  if (PyTritonOptions::callbackSyscallEntry){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and Std are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromLong(threadId));
    PyTuple_SetItem(args, 1, PyLong_FromLong(std));
    if (PyObject_CallObject(PyTritonOptions::callbackSyscallEntry, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSyscallExit(uint64 threadId, uint64 std) {
  // Check if there is a callback wich must be called after the syscall processing
  if (PyTritonOptions::callbackSyscallExit){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and Std are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromLong(threadId));
    PyTuple_SetItem(args, 1, PyLong_FromLong(std));
    if (PyObject_CallObject(PyTritonOptions::callbackSyscallExit, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::applyConfBeforeProcessing(IRBuilder *irb) {
  this->startAnalysisFromAddr(irb);
  this->startAnalysisFromOffset(irb);
  this->stopAnalysisFromAddr(irb);
  this->stopAnalysisFromOffset(irb);
  #ifndef LIGHT_VERSION
  this->taintMemFromAddr(irb);
  this->taintRegFromAddr(irb);
  this->untaintMemFromAddr(irb);
  this->untaintRegFromAddr(irb);
  #endif
}


void ProcessingPyConf::callbackRoutine(uint64 threadId, PyObject *callback) {
  PyObject *args = xPyTuple_New(1);
  PyTuple_SetItem(args, 0, PyLong_FromLong(threadId));
  if (PyObject_CallObject(callback, args) == nullptr){
    PyErr_Print();
    exit(1);
  }
  Py_DECREF(args);
}

