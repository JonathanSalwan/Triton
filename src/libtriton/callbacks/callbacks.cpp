//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <callbacks.hpp>
#include <exceptions.hpp>

#ifdef TRITON_PYTHON_BINDINGS
  #include <pythonObjects.hpp>
  #include <pythonUtils.hpp>
  #include <pythonXFunctions.hpp>
#endif



namespace triton {
  namespace callbacks {

    Callbacks::Callbacks() {
      this->isDefined = false;
    }


    Callbacks::Callbacks(const Callbacks& copy) {
      #ifdef TRITON_PYTHON_BINDINGS
      this->pyMemoryLoadCallbacks             = copy.pyMemoryLoadCallbacks;
      this->pyRegisterGetCallbacks            = copy.pyRegisterGetCallbacks;
      this->pySymbolicSimplificationCallbacks = copy.pySymbolicSimplificationCallbacks;
      #endif
      this->memoryLoadCallbacks               = copy.memoryLoadCallbacks;
      this->registerGetCallbacks              = copy.registerGetCallbacks;
      this->symbolicSimplificationCallbacks   = copy.symbolicSimplificationCallbacks;
      this->isDefined                         = copy.isDefined;
    }


    Callbacks::~Callbacks() {
    }


    void Callbacks::operator=(const Callbacks& copy) {
      #ifdef TRITON_PYTHON_BINDINGS
      this->pyMemoryLoadCallbacks             = copy.pyMemoryLoadCallbacks;
      this->pyRegisterGetCallbacks            = copy.pyRegisterGetCallbacks;
      this->pySymbolicSimplificationCallbacks = copy.pySymbolicSimplificationCallbacks;
      #endif
      this->memoryLoadCallbacks               = copy.memoryLoadCallbacks;
      this->registerGetCallbacks              = copy.registerGetCallbacks;
      this->symbolicSimplificationCallbacks   = copy.symbolicSimplificationCallbacks;
      this->isDefined                         = copy.isDefined;
    }


    void Callbacks::addCallback(triton::callbacks::memoryLoadCallback cb) {
      this->memoryLoadCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::registerGetCallback cb) {
      this->registerGetCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.push_back(cb);
      this->isDefined = true;
    }


    #ifdef TRITON_PYTHON_BINDINGS
    void Callbacks::addCallback(PyObject* function, triton::callbacks::callback_e kind) {
      switch (kind) {
        case MEMORY_LOAD:
          this->pyMemoryLoadCallbacks.push_back(function);
          break;
        case REGISTER_GET:
          this->pyRegisterGetCallbacks.push_back(function);
          break;
        case SYMBOLIC_SIMPLIFICATION:
          this->pySymbolicSimplificationCallbacks.push_back(function);
          break;
        default:
          throw triton::exceptions::Callbacks("Callbacks::addCallback(): Invalid kind of callback.");
      };
      this->isDefined = true;
    }
    #endif


    void Callbacks::removeCallback(triton::callbacks::memoryLoadCallback cb) {
      this->memoryLoadCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::registerGetCallback cb) {
      this->registerGetCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    #ifdef TRITON_PYTHON_BINDINGS
    void Callbacks::removeCallback(PyObject* function, triton::callbacks::callback_e kind) {
      switch (kind) {
        case MEMORY_LOAD:
          this->pyMemoryLoadCallbacks.remove(function);
          break;
        case REGISTER_GET:
          this->pyRegisterGetCallbacks.remove(function);
          break;
        case SYMBOLIC_SIMPLIFICATION:
          this->pySymbolicSimplificationCallbacks.remove(function);
          break;
        default:
          throw triton::exceptions::Callbacks("Callbacks::removeCallback(): Invalid kind of callback.");
      };

      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }
    #endif


    triton::ast::AbstractNode* Callbacks::processCallbacks(triton::callbacks::callback_e kind, triton::ast::AbstractNode* node) const {
      switch (kind) {
        case triton::callbacks::SYMBOLIC_SIMPLIFICATION: {
          // C++ callbacks
          std::list<triton::callbacks::symbolicSimplificationCallback>::const_iterator it1;
          for (it1 = this->symbolicSimplificationCallbacks.begin(); it1 != this->symbolicSimplificationCallbacks.end(); it1++) {
            node = (*it1)(node);
            if (node == nullptr)
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): You cannot return a nullptr node.");
          }

          #ifdef TRITON_PYTHON_BINDINGS
          // Python callbacks
          std::list<PyObject*>::const_iterator it2;
          for (it2 = this->pySymbolicSimplificationCallbacks.begin(); it2 != this->pySymbolicSimplificationCallbacks.end(); it2++) {

            /* Create function args */
            PyObject* args = triton::bindings::python::xPyTuple_New(1);
            PyTuple_SetItem(args, 0, triton::bindings::python::PyAstNode(node));

            /* Call the callback */
            PyObject* ret = PyObject_CallObject(*it2, args);

            /* Check the call */
            if (ret == nullptr) {
              PyErr_Print();
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): Fail to call the python callback.");
            }

            /* Check if the callback has returned a AbstractNode */
            if (!PyAstNode_Check(ret))
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): You must return a AstNode object.");

            /* Update node */
            node = PyAstNode_AsAstNode(ret);
            Py_DECREF(args);
          }
          #endif
          break;
        }
        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };

      return node;
    }


    void Callbacks::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::MemoryAccess& mem) const {
      switch (kind) {
        case triton::callbacks::MEMORY_LOAD: {
          // C++ callbacks
          std::list<triton::callbacks::memoryLoadCallback>::const_iterator it1;
          for (it1 = this->memoryLoadCallbacks.begin(); it1 != this->memoryLoadCallbacks.end(); it1++)
            (*it1)(mem.getAddress(), mem.getSize());

          #ifdef TRITON_PYTHON_BINDINGS
          // Python callbacks
          std::list<PyObject*>::const_iterator it2;
          for (it2 = this->pyMemoryLoadCallbacks.begin(); it2 != this->pyMemoryLoadCallbacks.end(); it2++) {

            /* Create function args */
            PyObject* args = triton::bindings::python::xPyTuple_New(2);
            PyTuple_SetItem(args, 0, triton::bindings::python::PyLong_FromUint64(mem.getAddress()));
            PyTuple_SetItem(args, 1, triton::bindings::python::PyLong_FromUint32(mem.getSize()));

            /* Call the callback */
            PyObject* ret = PyObject_CallObject(*it2, args);

            /* Check the call */
            if (ret == nullptr) {
              PyErr_Print();
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(MEMORY_LOAD): Fail to call the python callback.");
            }

            Py_DECREF(args);
          }
          #endif
          break;
        }

        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };
    }


    void Callbacks::processCallbacks(triton::callbacks::callback_e kind, const triton::arch::Register& reg) const {
      switch (kind) {
        case triton::callbacks::REGISTER_GET: {
          // C++ callbacks
          std::list<triton::callbacks::registerGetCallback>::const_iterator it1;
          for (it1 = this->registerGetCallbacks.begin(); it1 != this->registerGetCallbacks.end(); it1++)
            (*it1)(reg);

          #ifdef TRITON_PYTHON_BINDINGS
          // Python callbacks
          std::list<PyObject*>::const_iterator it2;
          for (it2 = this->pyRegisterGetCallbacks.begin(); it2 != this->pyRegisterGetCallbacks.end(); it2++) {

            /* Create function args */
            PyObject* args = triton::bindings::python::xPyTuple_New(1);
            PyTuple_SetItem(args, 0, triton::bindings::python::PyRegister(reg));

            /* Call the callback */
            PyObject* ret = PyObject_CallObject(*it2, args);

            /* Check the call */
            if (ret == nullptr) {
              PyErr_Print();
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(REGISTER_GET): Fail to call the python callback.");
            }

            Py_DECREF(args);
          }
          #endif
          break;
        }

        default:
          throw triton::exceptions::Callbacks("Callbacks::processCallbacks(): Invalid kind of callback for this C++ polymorphism.");
      };
    }


    triton::usize Callbacks::countCallbacks(void) const {
      triton::usize count = 0;

      count += this->memoryLoadCallbacks.size();
      count += this->registerGetCallbacks.size();
      count += this->symbolicSimplificationCallbacks.size();
      #ifdef TRITON_PYTHON_BINDINGS
      count += this->pyMemoryLoadCallbacks.size();
      count += this->pyRegisterGetCallbacks.size();
      count += this->pySymbolicSimplificationCallbacks.size();
      #endif

      return count;
    }

  }; /* callbacks namespace */
}; /* triton namespace */
