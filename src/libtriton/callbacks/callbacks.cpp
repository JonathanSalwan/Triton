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
      this->pyGetConcreteMemoryValueCallbacks   = copy.pyGetConcreteMemoryValueCallbacks;
      this->pyGetConcreteRegisterValueCallbacks = copy.pyGetConcreteRegisterValueCallbacks;
      this->pySymbolicSimplificationCallbacks   = copy.pySymbolicSimplificationCallbacks;
      #endif
      this->getConcreteMemoryValueCallbacks     = copy.getConcreteMemoryValueCallbacks;
      this->getConcreteRegisterValueCallbacks   = copy.getConcreteRegisterValueCallbacks;
      this->symbolicSimplificationCallbacks     = copy.symbolicSimplificationCallbacks;
      this->isDefined                           = copy.isDefined;
    }


    Callbacks::~Callbacks() {
    }


    void Callbacks::operator=(const Callbacks& copy) {
      #ifdef TRITON_PYTHON_BINDINGS
      this->pyGetConcreteMemoryValueCallbacks   = copy.pyGetConcreteMemoryValueCallbacks;
      this->pyGetConcreteRegisterValueCallbacks = copy.pyGetConcreteRegisterValueCallbacks;
      this->pySymbolicSimplificationCallbacks   = copy.pySymbolicSimplificationCallbacks;
      #endif
      this->getConcreteMemoryValueCallbacks     = copy.getConcreteMemoryValueCallbacks;
      this->getConcreteRegisterValueCallbacks   = copy.getConcreteRegisterValueCallbacks;
      this->symbolicSimplificationCallbacks     = copy.symbolicSimplificationCallbacks;
      this->isDefined                           = copy.isDefined;
    }


    void Callbacks::addCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
      this->getConcreteMemoryValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
      this->getConcreteRegisterValueCallbacks.push_back(cb);
      this->isDefined = true;
    }


    void Callbacks::addCallback(triton::callbacks::symbolicSimplificationCallback cb) {
      this->symbolicSimplificationCallbacks.push_back(cb);
      this->isDefined = true;
    }


    #ifdef TRITON_PYTHON_BINDINGS
    void Callbacks::addCallback(PyObject* function, triton::callbacks::callback_e kind) {
      switch (kind) {
        case GET_CONCRETE_MEMORY_VALUE:
          this->pyGetConcreteMemoryValueCallbacks.push_back(function);
          break;
        case GET_CONCRETE_REGISTER_VALUE:
          this->pyGetConcreteRegisterValueCallbacks.push_back(function);
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


    void Callbacks::removeAllCallbacks(void) {
      this->getConcreteMemoryValueCallbacks.clear();
      this->getConcreteRegisterValueCallbacks.clear();
      this->symbolicSimplificationCallbacks.clear();
      #ifdef TRITON_PYTHON_BINDINGS
      this->pyGetConcreteMemoryValueCallbacks.clear();
      this->pyGetConcreteRegisterValueCallbacks.clear();
      this->pySymbolicSimplificationCallbacks.clear();
      #endif
    }


    void Callbacks::removeCallback(triton::callbacks::getConcreteMemoryValueCallback cb) {
      this->getConcreteMemoryValueCallbacks.remove(cb);
      if (this->countCallbacks() == 0)
        this->isDefined = false;
    }


    void Callbacks::removeCallback(triton::callbacks::getConcreteRegisterValueCallback cb) {
      this->getConcreteRegisterValueCallbacks.remove(cb);
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
        case GET_CONCRETE_MEMORY_VALUE:
          this->pyGetConcreteMemoryValueCallbacks.remove(function);
          break;
        case GET_CONCRETE_REGISTER_VALUE:
          this->pyGetConcreteRegisterValueCallbacks.remove(function);
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
        case triton::callbacks::GET_CONCRETE_MEMORY_VALUE: {
          // C++ callbacks
          std::list<triton::callbacks::getConcreteMemoryValueCallback>::const_iterator it1;
          for (it1 = this->getConcreteMemoryValueCallbacks.begin(); it1 != this->getConcreteMemoryValueCallbacks.end(); it1++)
            (*it1)(const_cast<triton::arch::MemoryAccess&>(mem));

          #ifdef TRITON_PYTHON_BINDINGS
          // Python callbacks
          std::list<PyObject*>::const_iterator it2;
          for (it2 = this->pyGetConcreteMemoryValueCallbacks.begin(); it2 != this->pyGetConcreteMemoryValueCallbacks.end(); it2++) {

            /* Create function args */
            PyObject* args = triton::bindings::python::xPyTuple_New(1);
            PyTuple_SetItem(args, 0, triton::bindings::python::PyMemoryAccess(mem));

            /* Call the callback */
            PyObject* ret = PyObject_CallObject(*it2, args);

            /* Check the call */
            if (ret == nullptr) {
              PyErr_Print();
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(GET_CONCRETE_MEMORY_VALUE): Fail to call the python callback.");
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
        case triton::callbacks::GET_CONCRETE_REGISTER_VALUE: {
          // C++ callbacks
          std::list<triton::callbacks::getConcreteRegisterValueCallback>::const_iterator it1;
          for (it1 = this->getConcreteRegisterValueCallbacks.begin(); it1 != this->getConcreteRegisterValueCallbacks.end(); it1++)
            (*it1)(const_cast<triton::arch::Register&>(reg));

          #ifdef TRITON_PYTHON_BINDINGS
          // Python callbacks
          std::list<PyObject*>::const_iterator it2;
          for (it2 = this->pyGetConcreteRegisterValueCallbacks.begin(); it2 != this->pyGetConcreteRegisterValueCallbacks.end(); it2++) {

            /* Create function args */
            PyObject* args = triton::bindings::python::xPyTuple_New(1);
            PyTuple_SetItem(args, 0, triton::bindings::python::PyRegister(reg));

            /* Call the callback */
            PyObject* ret = PyObject_CallObject(*it2, args);

            /* Check the call */
            if (ret == nullptr) {
              PyErr_Print();
              throw triton::exceptions::Callbacks("Callbacks::processCallbacks(GET_CONCRETE_REGISTER_VALUE): Fail to call the python callback.");
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

      count += this->getConcreteMemoryValueCallbacks.size();
      count += this->getConcreteRegisterValueCallbacks.size();
      count += this->symbolicSimplificationCallbacks.size();
      #ifdef TRITON_PYTHON_BINDINGS
      count += this->pyGetConcreteMemoryValueCallbacks.size();
      count += this->pyGetConcreteRegisterValueCallbacks.size();
      count += this->pySymbolicSimplificationCallbacks.size();
      #endif

      return count;
    }

  }; /* callbacks namespace */
}; /* triton namespace */
