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


void ProcessingPyConf::startAnalysisFromAddr(reg_size addr) {
  // Check if the DSE must be start at this address
  if (PyTritonOptions::startAnalysisFromAddr.find(addr) != PyTritonOptions::startAnalysisFromAddr.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::startAnalysisFromOffset(reg_size offset) {
  // Check if the DSE must be start at this offset
  if (PyTritonOptions::startAnalysisFromOffset.find(offset) != PyTritonOptions::startAnalysisFromOffset.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::stopAnalysisFromAddr(reg_size addr) {
  // Check if the DSE must be stop at this address
  if (PyTritonOptions::stopAnalysisFromAddr.find(addr) != PyTritonOptions::stopAnalysisFromAddr.end())
    this->analysisTrigger->update(false);
}


void ProcessingPyConf::stopAnalysisFromOffset(reg_size offset) {
  // Check if the DSE must be stop at this offset
  if (PyTritonOptions::stopAnalysisFromOffset.find(offset) != PyTritonOptions::stopAnalysisFromOffset.end())
    this->analysisTrigger->update(false);
}


#ifndef LIGHT_VERSION

void ProcessingPyConf::taintMemFromAddr(reg_size addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is memory tainted via the python bindings
  std::list<reg_size> memsTainted = PyTritonOptions::taintMemFromAddr[addr];
  std::list<reg_size>::iterator it = memsTainted.begin();
  for ( ; it != memsTainted.end(); it++) {
    MemoryOperand mem(*it, 1);
    this->ap->taintMem(mem);
  }
}


void ProcessingPyConf::taintRegFromAddr(reg_size addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers tainted via the python bindings
  std::list<reg_size> regsTainted = PyTritonOptions::taintRegFromAddr[addr];
  std::list<reg_size>::iterator it = regsTainted.begin();
  for ( ; it != regsTainted.end(); it++) {
    RegisterOperand reg = createTmpReg(*it);
    this->ap->taintReg(reg);
  }
}


void ProcessingPyConf::untaintMemFromAddr(reg_size addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is memories untainted via the python bindings
  std::list<reg_size> memsUntainted = PyTritonOptions::untaintMemFromAddr[addr];
  std::list<reg_size>::iterator it = memsUntainted.begin();
  for ( ; it != memsUntainted.end(); it++) {
    MemoryOperand mem(*it, 1);
    this->ap->untaintMem(mem);
  }
}


void ProcessingPyConf::untaintRegFromAddr(reg_size addr) {
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers untainted via the python bindings
  std::list<reg_size> regsUntainted = PyTritonOptions::untaintRegFromAddr[addr];
  std::list<reg_size>::iterator it = regsUntainted.begin();
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


void ProcessingPyConf::callbackSignals(reg_size threadId, sint32 sig) {
  // Check if there is a callback wich must be called when a signal occurs
  if (PyTritonOptions::callbackSignals){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and sig are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromLongLong(threadId));
    PyTuple_SetItem(args, 1, Py_BuildValue("i", sig));
    if (PyObject_CallObject(PyTritonOptions::callbackSignals, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSyscallEntry(reg_size threadId, reg_size std) {
  // Check if there is a callback wich must be called before the syscall processing
  if (PyTritonOptions::callbackSyscallEntry){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and Std are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromLongLong(threadId));
    PyTuple_SetItem(args, 1, PyLong_FromLongLong(std));
    if (PyObject_CallObject(PyTritonOptions::callbackSyscallEntry, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackSyscallExit(reg_size threadId, reg_size std) {
  // Check if there is a callback wich must be called after the syscall processing
  if (PyTritonOptions::callbackSyscallExit){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * threadId and Std are sent to the callback. */
    PyObject *args = xPyTuple_New(2);
    PyTuple_SetItem(args, 0, PyLong_FromLongLong(threadId));
    PyTuple_SetItem(args, 1, PyLong_FromLongLong(std));
    if (PyObject_CallObject(PyTritonOptions::callbackSyscallExit, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackImageLoad(string imagePath, reg_size imageBase, reg_size imageSize) {
  // Check if there is a callback wich must be called when an image is loaded
  if (PyTritonOptions::callbackImageLoad){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * imagePath, imageBase and imageSize are sent to the callback. */
    PyObject *args = xPyTuple_New(3);
    PyTuple_SetItem(args, 0, PyString_FromString(imagePath.c_str()));
    PyTuple_SetItem(args, 1, PyLong_FromLongLong(imageBase));
    PyTuple_SetItem(args, 2, PyLong_FromLongLong(imageSize));
    if (PyObject_CallObject(PyTritonOptions::callbackImageLoad, args) == nullptr){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::applyConfBeforeProcessing(IRBuilder *irb) {
  reg_size addr = irb->getAddress();

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


void ProcessingPyConf::applyConfAfterProcessing(Inst *inst) {
  this->stopAnalysisFromAddr(inst->getAddress());
  this->stopAnalysisFromOffset(inst->getOffset());
}


void ProcessingPyConf::callbackRoutine(reg_size threadId, PyObject *callback) {
  PyObject *args = xPyTuple_New(1);
  PyTuple_SetItem(args, 0, PyLong_FromLongLong(threadId));
  if (PyObject_CallObject(callback, args) == nullptr){
    PyErr_Print();
    exit(1);
  }
  Py_DECREF(args);
}

