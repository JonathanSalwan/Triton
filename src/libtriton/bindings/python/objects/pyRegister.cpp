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

This object is used to represent a register operand according to the CPU architecture.

\subsection py_Register_example Example

~~~~~~~~~~~~~{.py}
>>> processing(inst)
>>> print inst
40000: mov ah, byte ptr [rdx + rcx*2 + 0x100]

>>> op0 = inst.getOperands()[0]
>>> print op0
ah:8 bv[15..8]

>>> op0.getName()
'ah'

>>> op0.getSize()
1

>>> op0.getBitSize()
8

>>> op0.getParent().getName()
'rax'
~~~~~~~~~~~~~

\subsection py_Register_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> ah = Register(REG.AH, 0x18)
>>> print ah
ah:8 bv[15..8]

>>> print ah.getBitSize()
8

>>> print hex(ah.getConcreteValue())
0x18L
~~~~~~~~~~~~~

\section Register_py_api Python API - Methods of the Register class
<hr>

- **getBitSize(void)**<br>
Returns the size (in bits) of the register as integer.<br>
e.g: `64`

- **getBitvector(void)**<br>
Returns the bitvector as \ref py_Bitvector_page.

- **getConcreteValue(void)**<br>
Returns the concrete value assigned to this register operand.

- **getName(void)**<br>
Returns the name of the register as string.<br>
e.g: `rbx`

- **getParent(void)**<br>
Returns the parent register as \ref py_Register_page.

- **getSize(void)**<br>
Returns the size (in bytes) of the register as integer.<br>
e.g: `8`

- **getType(void)**<br>
Returns type of the register as \ref py_OPERAND_page. In this case this function returns `OPERAND.REG`.

- **isValid(void)**<br>
Returns true if the register is valid.

- **isFlag(void)**<br>
Returns true if the register is a flag.

- **isRegister(void)**<br>
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

      //! Register destructor.
      void RegisterOperand_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyRegisterOperand_AsRegisterOperand(self);
        Py_DECREF(self);
      }


      static PyObject* RegisterOperand_getBitSize(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getBitSize());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_getBitvector(PyObject* self, PyObject* noarg) {
        try {
          return PyBitvector(*PyRegisterOperand_AsRegisterOperand(self));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_getConcreteValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyRegisterOperand_AsRegisterOperand(self)->getConcreteValue());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_getName(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PyRegisterOperand_AsRegisterOperand(self)->getName().c_str());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_getParent(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::RegisterOperand parent = PyRegisterOperand_AsRegisterOperand(self)->getParent();
          return PyRegisterOperand(parent);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_getSize(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getSize());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_getType(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("k", PyRegisterOperand_AsRegisterOperand(self)->getType());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_isValid(PyObject* self, PyObject* noarg) {
        try {
          if (PyRegisterOperand_AsRegisterOperand(self)->isValid())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_isRegister(PyObject* self, PyObject* noarg) {
        try {
          if (PyRegisterOperand_AsRegisterOperand(self)->isRegister())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_isTrusted(PyObject* self, PyObject* noarg) {
        try {
          if (PyRegisterOperand_AsRegisterOperand(self)->isTrusted())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_isFlag(PyObject* self, PyObject* noarg) {
        try {
          if (PyRegisterOperand_AsRegisterOperand(self)->isFlag())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_setConcreteValue(PyObject* self, PyObject* value) {
        try {
          triton::arch::RegisterOperand *reg;

          if (!PyLong_Check(value) && !PyInt_Check(value))
            return PyErr_Format(PyExc_TypeError, "Register::setConcretevalue(): Expected an integer as argument.");

          reg = PyRegisterOperand_AsRegisterOperand(self);
          if (reg->isFlag())
            return PyErr_Format(PyExc_TypeError, "Register::setConcreteValue(): You cannot set a concrete value on a flag.");

          reg->setConcreteValue(PyLong_AsUint512(value));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* RegisterOperand_setTrust(PyObject* self, PyObject* flag) {
        try {
          if (!PyBool_Check(flag))
            return PyErr_Format(PyExc_TypeError, "Register::setTrust(): Expected a boolean as argument.");
          PyRegisterOperand_AsRegisterOperand(self)->setTrust(PyLong_AsUint(flag));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int RegisterOperand_print(PyObject* self) {
        std::cout << PyRegisterOperand_AsRegisterOperand(self);
        return 0;
      }


      static PyObject* RegisterOperand_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyRegisterOperand_AsRegisterOperand(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Register methods.
      PyMethodDef RegisterOperand_callbacks[] = {
        {"getBitSize",        RegisterOperand_getBitSize,       METH_NOARGS,    ""},
        {"getBitvector",      RegisterOperand_getBitvector,     METH_NOARGS,    ""},
        {"getConcreteValue",  RegisterOperand_getConcreteValue, METH_NOARGS,    ""},
        {"getName",           RegisterOperand_getName,          METH_NOARGS,    ""},
        {"getParent",         RegisterOperand_getParent,        METH_NOARGS,    ""},
        {"getSize",           RegisterOperand_getSize,          METH_NOARGS,    ""},
        {"getType",           RegisterOperand_getType,          METH_NOARGS,    ""},
        {"isFlag",            RegisterOperand_isFlag,           METH_NOARGS,    ""},
        {"isRegister",        RegisterOperand_isRegister,       METH_NOARGS,    ""},
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
          (printfunc)RegisterOperand_print,           /* tp_print*/
          0,                                          /* tp_getattr*/
          0,                                          /* tp_setattr*/
          0,                                          /* tp_compare*/
          0,                                          /* tp_repr*/
          0,                                          /* tp_as_number*/
          0,                                          /* tp_as_sequence*/
          0,                                          /* tp_as_mapping*/
          0,                                          /* tp_hash */
          0,                                          /* tp_call*/
          (reprfunc)RegisterOperand_str,              /* tp_str*/
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


      PyObject* PyRegisterOperand(const triton::arch::RegisterOperand& reg) {
        RegisterOperand_Object* object;

        PyType_Ready(&RegisterOperand_Type);
        object = PyObject_NEW(RegisterOperand_Object, &RegisterOperand_Type);
        if (object != NULL)
          object->reg = new triton::arch::RegisterOperand(reg);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
