//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/register.hpp>
#include <triton/api.hpp>


namespace triton {
  namespace bindings {
    namespace python {

      static PyObject* AstContext_assert(PyObject* self, PyObject* expr) {
        if (!PyAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "assert_(): expected an AstNode as first argument");

        try {
          // FIXME : should we Check the context is the same?
          return PyAstNode(PyAstContext_AsAstContext(self)->assert_(PyAstNode_AsAstNode(expr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }

      //! AstContext methods.
      PyMethodDef AstContext_callbacks[] = {
        {"assert_",     AstContext_assert,       METH_O,    ""},
        {nullptr  ,               nullptr,            0,nullptr}
      };


      PyTypeObject AstContext_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "AstContext",                            /* tp_name */
        sizeof(AstContext_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        0,                                          /* tp_dealloc */
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
        0,                                          /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "AstContext objects",                    /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        AstContext_callbacks,                    /* tp_methods */
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


      PyObject* PyAstContext(triton::ast::AstContext& ctxt) {
        PyType_Ready(&AstContext_Type);
        AstContext_Object* object = PyObject_NEW(AstContext_Object, &AstContext_Type);

        if (object != nullptr)
          object->ctxt = &ctxt;

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
