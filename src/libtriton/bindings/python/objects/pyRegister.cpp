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

>>> regId = 1
>>> Register(regId)
rax:64 bv[63..0]
~~~~~~~~~~~~~

\section Register_py_api Python API - Methods of the Register class
<hr>

- <b>integer getBitSize(void)</b><br>
Returns the size (in bits) of the register.<br>
e.g: `64`

- <b>\ref py_Bitvector_page getBitvector(void)</b><br>
Returns the bitvector of the register.

- <b>integer getConcreteValue(void)</b><br>
Returns the concrete value assigned to this register operand.

- <b>string getName(void)</b><br>
Returns the name of the register.<br>
e.g: `rbx`

- <b>\ref py_Register_page getParent(void)</b><br>
Returns the parent register.

- <b>integer getSize(void)</b><br>
Returns the size (in bytes) of the register.<br>
e.g: `8`

- <b>\ref py_OPERAND_page getType(void)</b><br>
Returns type of the register. In this case this function returns `OPERAND.REG`.

- <b>bool isOverlapWith(\ref py_Register_page other)</b><br>
Returns true if `other` and `self` overlap.

- <b>void setConcreteValue(integer value)</b><br>
Sets a concrete value to this register.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Register destructor.
      void Register_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyRegister_AsRegister(self);
        Py_DECREF(self);
      }


      static PyObject* Register_getBitSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyRegister_AsRegister(self)->getBitSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getBitvector(PyObject* self, PyObject* noarg) {
        try {
          return PyBitvector(*PyRegister_AsRegister(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getConcreteValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyRegister_AsRegister(self)->getConcreteValue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getName(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PyRegister_AsRegister(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getParent(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Register parent = PyRegister_AsRegister(self)->getParent();
          return PyRegister(parent);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyRegister_AsRegister(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyRegister_AsRegister(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_isOverlapWith(PyObject* self, PyObject* reg2) {
        try {
          triton::arch::Register* reg1;

          if (!PyRegister_Check(reg2))
            return PyErr_Format(PyExc_TypeError, "Register::isOverlapWith(): Expected a Register as argument.");

          reg1 = PyRegister_AsRegister(self);
          if (reg1->isOverlapWith(*PyRegister_AsRegister(reg2)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_setConcreteValue(PyObject* self, PyObject* value) {
        triton::arch::Register* reg;

        if (!PyLong_Check(value) && !PyInt_Check(value))
          return PyErr_Format(PyExc_TypeError, "Register::setConcretevalue(): Expected an integer as argument.");

        try {
          reg = PyRegister_AsRegister(self);
          reg->setConcreteValue(PyLong_AsUint512(value));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int Register_print(PyObject* self) {
        std::cout << PyRegister_AsRegister(self);
        return 0;
      }


      static long Register_hash(PyObject* self) {
        return PyRegister_AsRegister(self)->getId();
      }


      static PyObject* Register_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyRegister_AsRegister(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_richcompare(PyObject* self, PyObject* other, int op)
      {
        PyObject* result    = nullptr;
        triton::uint32 id1  = 0;
        triton::uint32 id2  = 0;

        if (!PyRegister_Check(other)) {
          result = Py_NotImplemented;
        }

        else {
          id1 = PyRegister_AsRegister(self)->getId();
          id2 = PyRegister_AsRegister(other)->getId();

          switch (op) {
            case Py_LT:
                result = (id1 <  id2) ? Py_True : Py_False;
                break;
            case Py_LE:
                result = (id1 <= id2) ? Py_True : Py_False;
                break;
            case Py_EQ:
                result = (id1 == id2) ? Py_True : Py_False;
                break;
            case Py_NE:
                result = (id1 != id2) ? Py_True : Py_False;
                break;
            case Py_GT:
                result = (id1 >  id2) ? Py_True : Py_False;
                break;
            case Py_GE:
                result = (id1 >= id2) ? Py_True : Py_False;
                break;
          }
        }

        Py_INCREF(result);
        return result;
      }


      //! Register methods.
      PyMethodDef Register_callbacks[] = {
        {"getBitSize",        Register_getBitSize,       METH_NOARGS,    ""},
        {"getBitvector",      Register_getBitvector,     METH_NOARGS,    ""},
        {"getConcreteValue",  Register_getConcreteValue, METH_NOARGS,    ""},
        {"getName",           Register_getName,          METH_NOARGS,    ""},
        {"getParent",         Register_getParent,        METH_NOARGS,    ""},
        {"getSize",           Register_getSize,          METH_NOARGS,    ""},
        {"getType",           Register_getType,          METH_NOARGS,    ""},
        {"isOverlapWith",     Register_isOverlapWith,    METH_O,         ""},
        {"setConcreteValue",  Register_setConcreteValue, METH_O,         ""},
        {nullptr,             nullptr,                   0,              nullptr}
      };


      PyTypeObject Register_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Register",                                 /* tp_name */
        sizeof(Register_Object),                    /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Register_dealloc,               /* tp_dealloc */
        (printfunc)Register_print,                  /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        (hashfunc)Register_hash,                    /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)Register_str,                     /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "Register objects",                         /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        (richcmpfunc)Register_richcompare,          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Register_callbacks,                         /* tp_methods */
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


      PyObject* PyRegister(const triton::arch::Register& reg) {
        Register_Object* object;

        PyType_Ready(&Register_Type);
        object = PyObject_NEW(Register_Object, &Register_Type);
        if (object != NULL)
          object->reg = new triton::arch::Register(reg);

        return (PyObject*)object;
      }


      PyObject* PyRegister(const triton::arch::Register& reg, triton::uint512 concreteValue) {
        return PyRegister(reg, concreteValue, false);
      }


      PyObject* PyRegister(const triton::arch::Register& reg, triton::uint512 concreteValue, bool isImmutable) {
        PyType_Ready(&Register_Type);
        Register_Object* object = PyObject_NEW(Register_Object, &Register_Type);
        if (object != NULL)
          object->reg = new triton::arch::Register(reg.getId(), concreteValue, isImmutable);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
