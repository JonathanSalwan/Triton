//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/exceptions.hpp>
#include <triton/taintTag.hpp>


namespace triton {
  namespace bindings {
    namespace python {

      //! TaintTag destructor.
      void TaintTag_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyTaintTag_AsTaintTag(self);
        Py_DECREF(self);
      }


      static PyObject* TaintTag_getData(PyObject* self, PyObject* noarg) {
        try {
          return (PyObject*) PyTaintTag_AsTaintTag(self)->getData();
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TaintTag_str(PyObject* self) {
        try {
          std::stringstream str;
          str << "TaintTag(" << PyTaintTag_AsTaintTag(self)->getData() << ")";
          return PyString_FromFormat("%s", str.str().c_str());
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! TaintTag methods.
      PyMethodDef TaintTag_callbacks[] = {
        {"getData",           TaintTag_getData,       METH_NOARGS,    ""},
        {nullptr,             nullptr,                0,              nullptr}
      };


      PyTypeObject TaintTag_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "TaintTag",                                 /* tp_name */
        sizeof(TaintTag_Object),                    /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)TaintTag_dealloc,               /* tp_dealloc */
        0,                                          /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)TaintTag_str,                     /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "TaintTag objects",                         /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        TaintTag_callbacks,                         /* tp_methods */
        0,                                          /* tp_members */
        0,                                          /* tp_getset */
        0,                                          /* tp_base */
        0,                                          /* tp_dict */
        0,                                          /* tp_descr_get */
        0,                                          /* tp_descr_set */
        0,                                          /* tp_dictoffset */
        0,                                          /* tp_init */
        0,                                          /* tp_alloc */
        0,                                          /* tp_new */
        0,                                          /* tp_free */
        0,                                          /* tp_is_gc */
        0,                                          /* tp_bases */
        0,                                          /* tp_mro */
        0,                                          /* tp_cache */
        0,                                          /* tp_subclasses */
        0,                                          /* tp_weaklist */
        0,                                          /* tp_del */
        0                                           /* tp_version_tag */
      };


      PyObject* PyTaintTag(const triton::engines::taint::TaintTag& tag) {
        TaintTag_Object* object;

        PyType_Ready(&TaintTag_Type);
        object = PyObject_NEW(TaintTag_Object, &TaintTag_Type);
        if (object != NULL) {
          object->tag = new triton::engines::taint::TaintTag(tag);
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
