//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>
#include <registerOperand.hpp>



/*! \page py_Register_page Register
    \brief [**python api**] All information about the Register python object.

\tableofcontents

\section py_Register_description Description
<hr>

This object is used to represent a register according to the CPU architecture.

~~~~~~~~~~~~~{.py}
>>> ah = REG.AH
>>> ah
<Register at 0x7f8add745ae0>
>>> ah.getName()
'ah'
>>> ah.getSize()
1
>>> ah.getBitSize()
8
>>> ah.getParent().getName()
'rax'
~~~~~~~~~~~~~

\section Register_py_api Python API - Methods of the Register class
<hr>

- **getBitSize(void)**<br>
Returns the register's size in bits as integer.<br>
e.g: `64`

- **getBitvector(void)**<br>
Returns the bitvector as \ref py_Bitvector_page.

- **getConcreteValue(void)**<br>
Returns the register's concrete value.

- **getName(void)**<br>
Returns the register's name as string.<br>
e.g: `rbx`

- **getParent(void)**<br>
Returns the register's parent as string \ref py_Register_page.

- **getSize(void)**<br>
Returns the register's size in bytes as integer.<br>
e.g: `8`

- **getType(void)**<br>
Returns register's type in bytes as \ref py_OPERAND_page.<br>

- **isValid(void)**<br>
Returns true if the register is valid.

- **isFlag(void)**<br>
Returns true if the register is a flag.

- **isReg(void)**<br>
Returns true if the register is a register.

- **isTrusted(void)**<br>
True if this concrete register value is trusted and synchronized with the real CPU value.

- **setConcreteValue(integer value)**<br>
Sets a concrete value to this register. You cannot set a concrete value on a flag.

- **setTrust(bool flag)**<br>
Sets the trust flag.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Register's Destructor.
      void RegisterOperand_dealloc(PyObject* self) {
        delete PyRegisterOperand_AsRegisterOperand(self);
        Py_DECREF(self);
      }


      static PyObject* RegisterOperand_getBitSize(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getBitSize());
      }


      static PyObject* RegisterOperand_getBitvector(PyObject* self, PyObject* noarg) {
        return PyBitvector(*PyRegisterOperand_AsRegisterOperand(self));
      }


      static PyObject* RegisterOperand_getConcreteValue(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint128(PyRegisterOperand_AsRegisterOperand(self)->getConcreteValue());
      }


      static PyObject* RegisterOperand_getName(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("s", PyRegisterOperand_AsRegisterOperand(self)->getName().c_str());
      }


      static PyObject* RegisterOperand_getParent(PyObject* self, PyObject* noarg) {
        triton::arch::RegisterOperand parent = PyRegisterOperand_AsRegisterOperand(self)->getParent();
        return PyRegisterOperand(parent);
      }


      static PyObject* RegisterOperand_getSize(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getSize());
      }


      static PyObject* RegisterOperand_getType(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getType());
      }


      static PyObject* RegisterOperand_isValid(PyObject* self, PyObject* noarg) {
        if (PyRegisterOperand_AsRegisterOperand(self)->isValid())
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* RegisterOperand_isReg(PyObject* self, PyObject* noarg) {
        if (PyRegisterOperand_AsRegisterOperand(self)->isReg())
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* RegisterOperand_isTrusted(PyObject* self, PyObject* noarg) {
        if (PyRegisterOperand_AsRegisterOperand(self)->isTrusted())
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* RegisterOperand_isFlag(PyObject* self, PyObject* noarg) {
        if (PyRegisterOperand_AsRegisterOperand(self)->isFlag())
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* RegisterOperand_setConcreteValue(PyObject* self, PyObject* value) {
        triton::arch::RegisterOperand *reg;

        if (!PyLong_Check(value) && !PyInt_Check(value))
          return PyErr_Format(PyExc_TypeError, "setConcretevalue(): expected an integer as argument");

        reg = PyRegisterOperand_AsRegisterOperand(self);
        if (reg->isFlag())
          return PyErr_Format(PyExc_TypeError, "setConcreteValue(): You cannot set a concrete value on a flag.");

        reg->setConcreteValue(PyLong_AsUint128(value));
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* RegisterOperand_setTrust(PyObject* self, PyObject* flag) {
        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTrust(): expected a boolean as argument");
        PyRegisterOperand_AsRegisterOperand(self)->setTrust(PyLong_AsUint(flag));
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* Register_str(RegisterOperand_Object *obj) {
        std::stringstream str;
        str << *(obj->reg);
        return PyString_FromFormat("%s", str.str().c_str());
      }


      //! Register's methods.
      PyMethodDef RegisterOperand_callbacks[] = {
        {"getBitSize",        RegisterOperand_getBitSize,       METH_NOARGS,    ""},
        {"getBitvector",      RegisterOperand_getBitvector,     METH_NOARGS,    ""},
        {"getConcreteValue",  RegisterOperand_getConcreteValue, METH_NOARGS,    ""},
        {"getName",           RegisterOperand_getName,          METH_NOARGS,    ""},
        {"getParent",         RegisterOperand_getParent,        METH_NOARGS,    ""},
        {"getSize",           RegisterOperand_getSize,          METH_NOARGS,    ""},
        {"getType",           RegisterOperand_getType,          METH_NOARGS,    ""},
        {"isFlag",            RegisterOperand_isFlag,           METH_NOARGS,    ""},
        {"isReg",             RegisterOperand_isReg,            METH_NOARGS,    ""},
        {"isTrusted",         RegisterOperand_isTrusted,        METH_NOARGS,    ""},
        {"isValid",           RegisterOperand_isValid,          METH_NOARGS,    ""},
        {"setConcreteValue",  RegisterOperand_setConcreteValue, METH_O,         ""},
        {"setTrust",          RegisterOperand_setTrust,         METH_O,         ""},
        {nullptr,             nullptr,                          0,              nullptr}
      };


      PyTypeObject RegisterOperand_Type = {
          PyObject_HEAD_INIT(&PyType_Type)
          0,                                          /* ob_size*/
          "Register",                                 /* tp_name*/
          sizeof(RegisterOperand_Object),             /* tp_basicsize*/
          0,                                          /* tp_itemsize*/
          (destructor)RegisterOperand_dealloc,        /* tp_dealloc*/
          0,                                          /* tp_print*/
          0,                                          /* tp_getattr*/
          0,                                          /* tp_setattr*/
          0,                                          /* tp_compare*/
          0,                                          /* tp_repr*/
          0,                                          /* tp_as_number*/
          0,                                          /* tp_as_sequence*/
          0,                                          /* tp_as_mapping*/
          0,                                          /* tp_hash */
          0,                                          /* tp_call*/
          (reprfunc)Register_str,                     /* tp_str*/
          0,                                          /* tp_getattro*/
          0,                                          /* tp_setattro*/
          0,                                          /* tp_as_buffer*/
          Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
          "Register objects",                         /* tp_doc */
          0,                                          /* tp_traverse */
          0,                                          /* tp_clear */
          0,                                          /* tp_richcompare */
          0,                                          /* tp_weaklistoffset */
          0,                                          /* tp_iter */
          0,                                          /* tp_iternext */
          RegisterOperand_callbacks,                  /* tp_methods */
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
      };


      PyObject* PyRegisterOperand(triton::arch::RegisterOperand &reg) {
        RegisterOperand_Object *object;

        PyType_Ready(&RegisterOperand_Type);
        object = PyObject_NEW(RegisterOperand_Object, &RegisterOperand_Type);
        if (object != NULL)
          object->reg = new triton::arch::RegisterOperand(reg);

        return (PyObject* )object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
