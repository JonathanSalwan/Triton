
#include "ProcessingPyConf.h"
#include "TritonPyObject.h"
#include "xPyFunc.h"



ProcessingPyConf::ProcessingPyConf(AnalysisProcessor *ap, Trigger *analysisTrigger)
{
  this->ap = ap;
  this->analysisTrigger = analysisTrigger;
}


ProcessingPyConf::~ProcessingPyConf()
{
}


void ProcessingPyConf::startAnalysisFromAddr(IRBuilder *irb)
{
  // Check if the DSE must be start at this address
  if (PyTritonOptions::startAnalysisFromAddr.find(irb->getAddress()) != PyTritonOptions::startAnalysisFromAddr.end())
    this->analysisTrigger->update(true);
}


void ProcessingPyConf::stopAnalysisFromAddr(IRBuilder *irb)
{
  // Check if the DSE must be stop at this address
  if (PyTritonOptions::stopAnalysisFromAddr.find(irb->getAddress()) != PyTritonOptions::stopAnalysisFromAddr.end())
    this->analysisTrigger->update(false);
}


void ProcessingPyConf::taintRegFromAddr(IRBuilder *irb)
{
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers tainted via the python bindings
  std::list<uint64_t> regsTainted = PyTritonOptions::taintRegFromAddr[irb->getAddress()];
  std::list<uint64_t>::iterator it = regsTainted.begin();
  for ( ; it != regsTainted.end(); it++)
    this->ap->taintReg(*it);
}


void ProcessingPyConf::untaintRegFromAddr(IRBuilder *irb)
{
  // Apply this bindings only if the analysis is enable
  if (!this->analysisTrigger->getState())
    return;

  // Check if there is registers untainted via the python bindings
  std::list<uint64_t> regsUntainted = PyTritonOptions::untaintRegFromAddr[irb->getAddress()];
  std::list<uint64_t>::iterator it = regsUntainted.begin();
  for ( ; it != regsUntainted.end(); it++)
    this->ap->untaintReg(*it);
}


/*
 * When a callback is setup (triton.addCallback()), a class (Instruction) is
 * sent to the callback function as unique argument.
 */
void ProcessingPyConf::callbackAfter(Inst *inst, AnalysisProcessor *ap)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackAfter){

    /* Create the Instruction Python class */
    PyObject *instClass = PyInstruction(inst);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackAfter, args) == NULL){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackBefore(IRBuilder *irb, AnalysisProcessor *ap)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackBefore){

    /* Create the Instruction Python class */
    PyObject *instClass = PyInstruction(irb);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackBefore, args) == NULL){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::callbackFini(void)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (PyTritonOptions::callbackFini){

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * There is no argument sent to the callbacl. */
    PyObject *args = xPyTuple_New(0);
    if (PyObject_CallObject(PyTritonOptions::callbackFini, args) == NULL){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(args);
  }
}


void ProcessingPyConf::applyConfBeforeProcessing(IRBuilder *irb)
{
  this->startAnalysisFromAddr(irb);
  this->stopAnalysisFromAddr(irb);
  this->taintRegFromAddr(irb);
  this->untaintRegFromAddr(irb);
}

