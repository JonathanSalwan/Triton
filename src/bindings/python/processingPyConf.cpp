
#include "ProcessingPyConf.h"
#include "xPyFunc.h"



static PyObject *PySymbolicElement(SymbolicElement *element)
{
  PyObject *dictSEClass = xPyDict_New();
  PyDict_SetItemString(dictSEClass, "source", PyString_FromFormat("%s", element->getSource()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "destination", PyString_FromFormat("%s", element->getDestination()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "expression", PyString_FromFormat("%s", element->getExpression()->str().c_str()));
  PyDict_SetItemString(dictSEClass, "id", PyInt_FromLong(element->getID()));
  PyDict_SetItemString(dictSEClass, "isTainted", PyBool_FromLong(element->isTainted));

  PyObject *SEClassName = xPyString_FromString("SymbolicElement");
  PyObject *SEClass  = xPyClass_New(NULL, dictSEClass, SEClassName);

  return SEClass;
}


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
 *
 *
 * Class Instruction:
 *
 * - address (integer)
 * - threadId (integer)
 * - assembly (string)
 * - symbolicElements (list of SymbolicElement)
 *
 *
 * Class SymbolicElement:
 *
 * - source (string)
 * - destination (string)
 * - expression (string)
 * - id (integer)
 * - isTainted (bool)
 *
 */
void ProcessingPyConf::callbackAfter(Inst *inst, const ContextHandler &ctxH)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackAfter){

    /* Create the class dictionary */
    PyObject *dictInstClass = xPyDict_New();
    PyDict_SetItemString(dictInstClass, "address", PyInt_FromLong(inst->getAddress()));
    PyDict_SetItemString(dictInstClass, "threadId", PyInt_FromLong(inst->getThreadId()));
    PyDict_SetItemString(dictInstClass, "assembly", PyString_FromFormat("%s", inst->getDisassembly().c_str()));

    /* Setup the symbolic element list */
    PyObject *SEList                         = xPyList_New(inst->numberOfElements());
    std::list<SymbolicElement*> symElements  = inst->getSymbolicElements();
    std::list<SymbolicElement*>::iterator it = symElements.begin();

    Py_ssize_t index = 0;
    for ( ; it != symElements.end(); it++){
      PyList_SetItem(SEList, index, PySymbolicElement(*it));
      index++;
    }

    PyDict_SetItemString(dictInstClass, "symbolicElements", SEList);

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

    /* Go through all symbolicElements in SEList. */
    /* Free all items in the symbolicElement class. */
    for (index = 0; index < PyList_Size(SEList); index++){
      /* Get the object in the list */
      PyObject *o = PyList_GetItem(SEList, index);
      /* Cast the PyObject to PyClassObject */
      PyClassObject *co = reinterpret_cast<PyClassObject*>(o);
      /* Free the class name object */
      Py_DECREF(co->cl_name);
      /* Clear/Free the class dictionary items */
      PyDict_Clear(co->cl_dict);
      /* Free the class dictionary object */
      Py_DECREF(co->cl_dict);
      /* Free the initial object */
      Py_DECREF(o);
      /* Next object */
      index++;
    }

    PyDict_Clear(dictInstClass);  /* Clear all items in the dictionary */
    Py_DECREF(SEList);            /* Free the allocated symbolic element list */
    Py_DECREF(dictInstClass);     /* Free the allocated dictionary */
    Py_DECREF(instClassName);     /* Free the allocated Inst class name */
    Py_DECREF(args);              /* Free the allocated tuple */
  }
}


void ProcessingPyConf::callbackBefore(IRBuilder *irb, const ContextHandler &ctxH)
{
  // Check if there is a callback wich must be called at each instruction instrumented
  if (this->analysisTrigger->getState() && PyTritonOptions::callbackBefore){

    /* Create the class dictionary */
    PyObject *dictInstClass = xPyDict_New();
    PyDict_SetItemString(dictInstClass, "address", PyInt_FromLong(irb->getAddress()));
    PyDict_SetItemString(dictInstClass, "threadId", PyInt_FromLong(ctxH.getThreadId()));
    PyDict_SetItemString(dictInstClass, "assembly", PyString_FromFormat("%s", irb->getDisassembly().c_str()));
    /* Before the processing, the symbolic element list is empty */
    PyObject *SEList = xPyList_New(0);
    PyDict_SetItemString(dictInstClass, "symbolicElements", SEList);

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

    Py_DECREF(SEList);        /* Free the allocated symbolic element list */
    Py_DECREF(dictInstClass); /* Free the allocated dictionary */
    Py_DECREF(instClassName); /* Free the allocated Inst class name */
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

