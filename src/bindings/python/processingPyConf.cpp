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


void ProcessingPyConf::startAnalysisFromAddr(__uint addr) {
  // Check if the DSE must be start at this address
  if (PyTritonOptions::startAnalysisFromAddr.find(addr) != PyTritonOptions::startAnalysisFromAddr.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::startAnalysisFromOffset(__uint offset) {
  // Check if the DSE must be start at this offset
  if (PyTritonOptions::startAnalysisFromOffset.find(offset) != PyTritonOptions::startAnalysisFromOffset.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::stopAnalysisFromAddr(__uint addr) {
  // Check if the DSE must be stop at this address
  if (PyTritonOptions::stopAnalysisFromAddr.find(addr) != PyTritonOptions::stopAnalysisFromAddr.end())
    this->analysisTrigger->update(false);
}


void ProcessingPyConf::stopAnalysisFromOffset(__uint offset) {
  // Check if the DSE must be stop at this offset
  if (PyTritonOptions::stopAnalysisFromOffset.find(offset) != PyTritonOptions::stopAnalysisFromOffset.end())
    this->analysisTrigger->update(false);
}


#ifndef LIGHT_VERSION

void ProcessingPyConf::taintMemFromAddr(__uint addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is memory tainted via the python bindings
  std::list<__uint> memsTainted = PyTritonOptions::taintMemFromAddr[addr];
  std::list<__uint>::iterator it = memsTainted.begin();
  for ( ; it != memsTainted.end(); it++) {
    MemoryOperand mem(*it, 1);
    this->ap->taintMem(mem);
  }
}


void ProcessingPyConf::taintRegFromAddr(__uint addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers tainted via the python bindings
  std::list<__uint> regsTainted = PyTritonOptions::taintRegFromAddr[addr];
  std::list<__uint>::iterator it = regsTainted.begin();
  for ( ; it != regsTainted.end(); it++) {
    RegisterOperand reg = createTmpReg(*it);
    this->ap->taintReg(reg);
  }
}


void ProcessingPyConf::untaintMemFromAddr(__uint addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is memories untainted via the python bindings
  std::list<__uint> memsUntainted = PyTritonOptions::untaintMemFromAddr[addr];
  std::list<__uint>::iterator it = memsUntainted.begin();
  for ( ; it != memsUntainted.end(); it++) {
    MemoryOperand mem(*it, 1);
    this->ap->untaintMem(mem);
  }
}


void ProcessingPyConf::untaintRegFromAddr(__uint addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers untainted via the python bindings
  std::list<__uint> regsUntainted = PyTritonOptions::untaintRegFromAddr[addr];
  std::list<__uint>::iterator it = regsUntainted.begin();
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
void ProcessingPyConf::callbackAfter(Inst *inst) {
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


void ProcessingPyConf::callbackBefore(Inst *inst) {
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


void ProcessingPyConf::callbackBeforeIRProc(IRBuilder *irb) {
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


void ProcessingPyConf::callbackSignals(__uint threadId, sint32 sig) {
  // Check if there is a callback wich must be called when a signal occurs
  if (PyTritonOptions::callbackSignals){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and sig are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromUint(threadId));
    PyTuple_SetItem(args, 1, Py_BuildValue("i", sig));
    if (PyObject_CallObject(PyTritonOptions::callbackSignals, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSyscallEntry(__uint threadId, __uint std) {
  // Check if there is a callback wich must be called before the syscall processing
  if (PyTritonOptions::callbackSyscallEntry){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and Std are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromUint(threadId));
    PyTuple_SetItem(args, 1, PyLong_FromUint(std));
    if (PyObject_CallObject(PyTritonOptions::callbackSyscallEntry, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSyscallExit(__uint threadId, __uint std) {
  // Check if there is a callback wich must be called after the syscall processing
  if (PyTritonOptions::callbackSyscallExit){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and Std are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromUint(threadId));
    PyTuple_SetItem(args, 1, PyLong_FromUint(std));
    if (PyObject_CallObject(PyTritonOptions::callbackSyscallExit, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackImageLoad(string imagePath, __uint imageBase, __uint imageSize) {
  // Check if there is a callback wich must be called when an image is loaded
  if (PyTritonOptions::callbackImageLoad){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * imagePath, imageBase and imageSize are sent to the callback. */
    PyObject *args = xPyTuple_New(3);
    PyTuple_SetItem(args, 0, PyString_FromString(imagePath.c_str()));
    PyTuple_SetItem(args, 1, PyLong_FromUint(imageBase));
    PyTuple_SetItem(args, 2, PyLong_FromUint(imageSize));
    if (PyObject_CallObject(PyTritonOptions::callbackImageLoad, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::applyConfBeforeProcessing(IRBuilder *irb) {
  __uint addr = irb->getAddress();

  this->startAnalysisFromAddr(addr);
  this->startAnalysisFromOffset(addr);
  #ifndef LIGHT_VERSION
  this->taintMemFromAddr(addr);
  this->taintRegFromAddr(addr);
  this->untaintMemFromAddr(addr);
  this->untaintRegFromAddr(addr);
  #endif
}


void ProcessingPyConf::applyConfAfterProcessing(IRBuilder *irb) {
  this->stopAnalysisFromAddr(irb->getAddress());
  this->stopAnalysisFromOffset(irb->getOffset());
}


void ProcessingPyConf::callbackRoutine(__uint threadId, PyObject *callback) {
  PyObject *args = xPyTuple_New(1);
  PyTuple_SetItem(args, 0, PyLong_FromUint(threadId));
  if (PyObject_CallObject(callback, args) == nullptr){
    PyErr_Print();
    exit(1);
  }
  Py_DECREF(args);
}

