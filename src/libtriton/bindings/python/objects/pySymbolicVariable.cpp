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
#include <triton/symbolicVariable.hpp>



/* setup doctest context

>>> from triton import TritonContext, REG, ARCH
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

*/

/*! \page py_SymbolicVariable_page SymbolicVariable
    \brief [**python api**] All information about the SymbolicVariable python object.

\tableofcontents

\section py_SymbolicVariable_description Description
<hr>

This object is used to represent a symbolic variable.

~~~~~~~~~~~~~{.py}
>>> symvar = ctxt.convertRegisterToSymbolicVariable(ctxt.registers.rax)
>>> print symvar
SymVar_0:64

~~~~~~~~~~~~~

\section SymbolicVariable_py_api Python API - Methods of the SymbolicVariable class
<hr>

- <b>integer getBitSize(void)</b><br>
Returns the size of the symbolic variable.

- <b>string getComment(void)</b><br>
Returns the comment (if exists) of the symbolic variable.

- <b>integer getId(void)</b><br>
Returns the id of the symbolic variable. This id is always unique.<br>
e.g: `18`

- <b>string getName(void)</b><br>
Returns name of the the symbolic variable.<br>
e.g: `SymVar_18`

- <b>integer getOrigin(void)</b><br>
Returns the origin according to the \ref py_SYMBOLIC_page value.<br>
If `getType()` returns triton::engines::symbolic::REGISTER_VARIABLE, so `getOrigin()` returns the id of the register.<br>
Otherwise, if `getType()` returns triton::engines::symbolic::MEMORY_VARIABLE, so `getOrigin()` returns the address of the memory access.<br>
Then, if `getType()` returns triton::engines::symbolic::UNDEFINED_VARIABLE, so `getOrigin()` returns `0`.

- <b>\ref py_SYMBOLIC_page getType(void)</b><br>
Returns the type of the symbolic variable.<br>
e.g: `SYMBOLIC.REGISTER_VARIABLE`

- <b>void setComment(string comment)</b><br>
Sets a comment to the symbolic variable.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! SymbolicVariable destructor.
      void SymbolicVariable_dealloc(PyObject* self) {
        std::cout << std::flush;
        PySymbolicVariable_AsSymbolicVariable(self) = nullptr; // decref the shared_ptr
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static PyObject* SymbolicVariable_getAlias(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PySymbolicVariable_AsSymbolicVariable(self)->getAlias().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_getName(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PySymbolicVariable_AsSymbolicVariable(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_getId(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUsize(PySymbolicVariable_AsSymbolicVariable(self)->getId());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PySymbolicVariable_AsSymbolicVariable(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_getOrigin(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PySymbolicVariable_AsSymbolicVariable(self)->getOrigin());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_getBitSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PySymbolicVariable_AsSymbolicVariable(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_getComment(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PySymbolicVariable_AsSymbolicVariable(self)->getComment().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_setAlias(PyObject* self, PyObject* alias) {
        try {
          if (!PyString_Check(alias))
            return PyErr_Format(PyExc_TypeError, "SymbolicVariable::setAlias(): Expected a string as argument.");
          PySymbolicVariable_AsSymbolicVariable(self)->setAlias(PyString_AsString(alias));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_setComment(PyObject* self, PyObject* comment) {
        try {
          if (!PyString_Check(comment))
            return PyErr_Format(PyExc_TypeError, "SymbolicVariable::setComment(): Expected a string as argument.");
          PySymbolicVariable_AsSymbolicVariable(self)->setComment(PyString_AsString(comment));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int SymbolicVariable_print(PyObject* self) {
        std::cout << PySymbolicVariable_AsSymbolicVariable(self);
        return 0;
      }


      static PyObject* SymbolicVariable_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PySymbolicVariable_AsSymbolicVariable(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicVariable_new(PyTypeObject* type, PyObject* args, PyObject* kwds) {
        return type->tp_alloc(type, 0);
      }


      static int SymbolicVariable_init(AstNode_Object* self, PyObject* args, PyObject* kwds) {
        return 0;
      }


      //! SymbolicVariable methods.
      PyMethodDef SymbolicVariable_callbacks[] = {
        {"getAlias",          SymbolicVariable_getAlias,          METH_NOARGS,    ""},
        {"getBitSize",        SymbolicVariable_getBitSize,        METH_NOARGS,    ""},
        {"getComment",        SymbolicVariable_getComment,        METH_NOARGS,    ""},
        {"getId",             SymbolicVariable_getId,             METH_NOARGS,    ""},
        {"getName",           SymbolicVariable_getName,           METH_NOARGS,    ""},
        {"getOrigin",         SymbolicVariable_getOrigin,         METH_NOARGS,    ""},
        {"getType",           SymbolicVariable_getType,           METH_NOARGS,    ""},
        {"setAlias",          SymbolicVariable_setAlias,          METH_O,         ""},
        {"setComment",        SymbolicVariable_setComment,        METH_O,         ""},
        {nullptr,             nullptr,                            0,              nullptr}
      };


      PyTypeObject SymbolicVariable_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "SymbolicVariable",                         /* tp_name */
        sizeof(SymbolicVariable_Object),            /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)SymbolicVariable_dealloc,       /* tp_dealloc */
        (printfunc)SymbolicVariable_print,          /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)SymbolicVariable_str,             /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "SymbolicVariable objects",                 /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        SymbolicVariable_callbacks,                 /* tp_methods */
        0,                                          /* tp_members */
        0,                                          /* tp_getset */
        0,                                          /* tp_base */
        0,                                          /* tp_dict */
        0,                                          /* tp_descr_get */
        0,                                          /* tp_descr_set */
        0,                                          /* tp_dictoffset */
        (initproc)SymbolicVariable_init,            /* tp_init */
        0,                                          /* tp_alloc */
        (newfunc)SymbolicVariable_new,              /* tp_new */
        0,                                          /* tp_free */
        0,                                          /* tp_is_gc */
        0,                                          /* tp_bases */
        0,                                          /* tp_mro */
        0,                                          /* tp_cache */
        0,                                          /* tp_subclasses */
        0,                                          /* tp_weaklist */
        (destructor)SymbolicVariable_dealloc,       /* tp_del */
        0                                           /* tp_version_tag */
      };


      PyObject* PySymbolicVariable(const triton::engines::symbolic::SharedSymbolicVariable& symVar) {
        if (symVar == nullptr) {
          Py_INCREF(Py_None);
          return Py_None;
        }

        PyType_Ready(&SymbolicVariable_Type);
        // Build the new object the python way (calling operator() on the type) as
        // it crash otherwise (certainly due to incorrect shared_ptr initialization).
        auto* object = (triton::bindings::python::SymbolicVariable_Object*)PyObject_CallObject((PyObject*)&SymbolicVariable_Type, nullptr);
        if (object != NULL) {
          object->symVar = symVar;
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
