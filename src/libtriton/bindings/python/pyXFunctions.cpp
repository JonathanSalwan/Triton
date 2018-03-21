//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonXFunctions.hpp>
#include <iostream>



namespace triton {
  namespace bindings {
    namespace python {

      static inline void notEnoughMemory(void) {
        std::cerr << "[ERROR] Not enough memory for allocation" << std::endl;
        exit(-1);
      }


      PyObject* xPyDict_New(void) {
        PyObject* dict = PyDict_New();
        if (!dict)
          notEnoughMemory();
        return dict;
      }


      PyObject* xPyList_New(Py_ssize_t len) {
        PyObject* list = PyList_New(len);
        if (!list)
          notEnoughMemory();
        return list;
      }


      PyObject* xPyTuple_New(Py_ssize_t len) {
        PyObject* tuple = PyTuple_New(len);
        if (!tuple)
          notEnoughMemory();
        return tuple;
      }


      PyObject* xPyString_FromString(const char *v) {
        PyObject* s = PyString_FromString(v);
        if (!s)
          notEnoughMemory();
        return s;
      }


      PyObject* xPyClass_New(PyObject* b, PyObject* d, PyObject* n) {
        PyObject* c = PyClass_New(b, d, n);

        if (!c)
          notEnoughMemory();

        Py_CLEAR(b);
        Py_CLEAR(d);
        Py_CLEAR(n);

        return c;
      }


      int xPyDict_SetItemString(PyObject* p, const char* key, PyObject* val) {
        int r = PyDict_SetItemString(p, key, val);
        Py_DECREF(val);
        return r;
      }


      int xPyDict_SetItem(PyObject* p, PyObject* key, PyObject* val) {
        int r = PyDict_SetItem(p, key, val);
        Py_DECREF(val);
        Py_DECREF(key);
        return r;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
