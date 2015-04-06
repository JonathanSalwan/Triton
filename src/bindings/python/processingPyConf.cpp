
#include "ProcessingPyConf.h"
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


void ProcessingPyConf::callbackBefore(IRBuilder *irb, const ContextHandler &ctxH)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackBefore){

    /* Create a dictionary */
    PyObject *dictInstClass = xPyDict_New();
    PyDict_SetItemString(dictInstClass, "address", PyInt_FromLong(irb->getAddress()));
    PyDict_SetItemString(dictInstClass, "threadId", PyInt_FromLong(ctxH.getThreadId()));
    PyDict_SetItemString(dictInstClass, "assembly", PyString_FromFormat("%s", irb->getDisassembly().c_str()));
    /* Before the processing, the expression list is empty */
    PyObject *listExpr = xPyList_New(0);
    PyDict_SetItemString(dictInstClass, "expressions", listExpr);

    /* Create the Instruction class */
    PyObject *instClassName = xPyString_FromString("Instruction");
    PyObject *instClass  = xPyClass_New(NULL, dictInstClass, instClassName);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackBefore, args) == NULL){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(listExpr);      /* Free the allocated expressions list */
    Py_DECREF(dictInstClass); /* Free the allocated dictionary */
    Py_DECREF(instClassName); /* Free the allocated Inst class name */
    Py_DECREF(instClass);     /* Free the allocated Inst class */
    Py_DECREF(args);          /* Free the allocated tuple */
  }
}


void ProcessingPyConf::callbackAfter(Inst *inst, const ContextHandler &ctxH)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackAfter){

    /* Create a dictionary */
    PyObject *dictInstClass = xPyDict_New();
    PyDict_SetItemString(dictInstClass, "address", PyInt_FromLong(inst->getAddress()));
    PyDict_SetItemString(dictInstClass, "threadId", PyInt_FromLong(inst->getThreadId()));
    PyDict_SetItemString(dictInstClass, "assembly", PyString_FromFormat("%s", inst->getDisassembly().c_str()));

    /* Setup the expression list */
    PyObject *listExpr                       = xPyList_New(inst->numberOfElements());
    std::list<SymbolicElement*> elements     = inst->getSymbolicElements();
    std::list<SymbolicElement*>::iterator it = elements.begin();
    
    uint64_t index = 0;
    for ( ; it != elements.end(); it++){
      PyList_SetItem(listExpr, index, PyString_FromFormat("%s", (*it)->getExpression()->str().c_str()));
      index++;
    }

    PyDict_SetItemString(dictInstClass, "expressions", listExpr);

    /* Create the Instruction class */
    PyObject *instClassName = xPyString_FromString("Instruction");
    PyObject *instClass  = xPyClass_New(NULL, dictInstClass, instClassName);

    /* CallObject needs a tuple. The size of the tuple is the number of arguments.
     * Triton sends only one argument to the callback. This argument is the Instruction
     * class and contains all information. */
    PyObject *args = xPyTuple_New(1);
    PyTuple_SetItem(args, 0, instClass);
    if (PyObject_CallObject(PyTritonOptions::callbackAfter, args) == NULL){
      PyErr_Print();
      exit(1);
    }

    Py_DECREF(listExpr);      /* Free the allocated expressions list */
    Py_DECREF(dictInstClass); /* Free the allocated dictionary */
    Py_DECREF(instClassName); /* Free the allocated Inst class name */
    Py_DECREF(instClass);     /* Free the allocated Inst class */
    Py_DECREF(args);          /* Free the allocated tuple */
  }
}


void ProcessingPyConf::applyConfBeforeProcessing(IRBuilder *irb, CONTEXT *ctx, THREADID threadId)
{
  this->startAnalysisFromAddr(irb);
  this->stopAnalysisFromAddr(irb);
  this->taintRegFromAddr(irb);
  this->untaintRegFromAddr(irb);
}

