
#include "ProcessingPyConf.h"


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
  // Check if there is registers tainted via the python bindings
  std::list<uint64_t> regsTainted = PyTritonOptions::taintRegFromAddr[irb->getAddress()];
  std::list<uint64_t>::iterator it = regsTainted.begin();
  for ( ; it != regsTainted.end(); it++)
    this->ap->taintReg(*it);
}


void ProcessingPyConf::untaintRegFromAddr(IRBuilder *irb)
{
  // Check if there is registers untainted via the python bindings
  std::list<uint64_t> regsUntainted = PyTritonOptions::untaintRegFromAddr[irb->getAddress()];
  std::list<uint64_t>::iterator it = regsUntainted.begin();
  for ( ; it != regsUntainted.end(); it++)
    this->ap->untaintReg(*it);
}


void ProcessingPyConf::callbackBefore(IRBuilder *irb, THREADID threadId)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackBefore){
    PyObject *args = PyTuple_New(2);
    PyTuple_SetItem(args, 0, PyInt_FromLong(irb->getAddress())); // TODO: Find a way to convert irb to python module
    PyTuple_SetItem(args, 1, PyInt_FromLong(threadId));
    if (PyObject_CallObject(PyTritonOptions::callbackBefore, args) == NULL){
      PyErr_Print();
      exit(1);
    }
    Py_DECREF(args); /* Free the allocated tuple */
  }
}


void ProcessingPyConf::callbackAfter(IRBuilder *irb, THREADID threadId)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackAfter){
    PyObject *args = PyTuple_New(2);
    PyTuple_SetItem(args, 0, PyInt_FromLong(irb->getAddress())); // TODO: Find a way to convert irb to python module
    PyTuple_SetItem(args, 1, PyInt_FromLong(threadId));
    if (PyObject_CallObject(PyTritonOptions::callbackAfter, args) == NULL){
      PyErr_Print();
      exit(1);
    }
    Py_DECREF(args); /* Free the allocated tuple */
  }
}


void ProcessingPyConf::applyConfBefore(IRBuilder *irb, CONTEXT *ctx, THREADID threadId)
{
  this->startAnalysisFromAddr(irb);
  this->stopAnalysisFromAddr(irb);
  this->taintRegFromAddr(irb);
  this->untaintRegFromAddr(irb);
  this->callbackBefore(irb, threadId);
}


void ProcessingPyConf::applyConfAfter(IRBuilder *irb, CONTEXT *ctx, THREADID threadId)
{
  this->callbackAfter(irb, threadId);
}


