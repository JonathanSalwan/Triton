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
#include <triton/tag.hpp>


namespace triton {
  namespace bindings {
    namespace python {

      //! Tag destructor.
      void Tag_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyTag_AsTag(self);
        Py_DECREF(self);
      }


      static PyObject* Tag_getData(PyObject* self, PyObject* noarg) {
        try {
          return (PyObject*) PyString_FromString(PyTag_AsTag(self)->getData()->c_str());
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Tag_str(PyObject* self) {
        try {
          std::stringstream str;
          // prints the pointer address of the stored string
          str << "Tag(" << PyTag_AsTag(self)->getData() << ")";
          return PyString_FromFormat("%s", str.str().c_str());
        } catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Tag methods.
      PyMethodDef Tag_callbacks[] = {
        {"getData",           Tag_getData,    METH_NOARGS,    ""},
        {nullptr,             nullptr,        0,              nullptr}
      };


      PyTypeObject Tag_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Tag",                                      /* tp_name */
        sizeof(Tag_Object),                         /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Tag_dealloc,                    /* tp_dealloc */
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
        (reprfunc)Tag_str,                          /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "Tag objects",                              /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Tag_callbacks,                              /* tp_methods */
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


      PyObject* PyTag(const triton::engines::taint::Tag& tag) {
        Tag_Object* object;

        PyType_Ready(&Tag_Type);
        object = PyObject_NEW(Tag_Object, &Tag_Type);
        if (object != NULL) {
          object->tag = new triton::engines::taint::Tag(tag);
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
