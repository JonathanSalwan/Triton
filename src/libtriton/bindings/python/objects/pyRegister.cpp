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
#include <triton/register.hpp>



/* setup doctest context

>>> from triton import ARCH, TritonContext, Instruction, REG
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> inst = Instruction("\x8A\xA4\x4A\x00\x01\x00\x00")
>>> inst.setAddress(0x40000)

*/

/*! \page py_Register_page Register
    \brief [**python api**] All information about the Register python object.

\tableofcontents

\section py_Register_description Description
<hr>

This object is used to represent a register operand according to the CPU architecture.


\subsection py_Register_example Example

~~~~~~~~~~~~~{.py}
>>> ctxt.processing(inst)
True
>>> print inst
0x40000: mov ah, byte ptr [rdx + rcx*2 + 0x100]

>>> op0 = inst.getOperands()[0]
>>> print op0
ah:8 bv[15..8]

>>> op0.getName()
'ah'

>>> op0.getSize()
1L

>>> op0.getBitSize()
8L

>>> ctxt.getParentRegister(op0).getName()
'rax'

~~~~~~~~~~~~~

\subsection py_Register_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> ah = ctxt.getRegister(REG.X86_64.AH)
>>> print ah
ah:8 bv[15..8]

>>> print ah.getBitSize()
8

>>> print ctxt.registers.rax
rax:64 bv[63..0]

~~~~~~~~~~~~~

\section Register_py_api Python API - Methods of the Register class
<hr>

- <b>integer getBitSize(void)</b><br>
Returns the size (in bits) of the register.<br>
e.g: `64`

- <b>\ref py_BitsVector_page getBitvector(void)</b><br>
Returns the bitvector of the register.

- <b>\ref py_REG_page getId(void)</b><br>
Returns the enum of the register.<br>
e.g: `REG.X86_64.RBX`

- <b>string getName(void)</b><br>
Returns the name of the register.<br>
e.g: `rbx`

- <b>integer getSize(void)</b><br>
Returns the size (in bytes) of the register.<br>
e.g: `8`

- <b>\ref py_OPERAND_page getType(void)</b><br>
Returns type of the register. In this case this function returns `OPERAND.REG`.

- <b>bool isOverlapWith(\ref py_Register_page other)</b><br>
Returns true if `other` and `self` overlap.

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
          return PyBitsVector(*PyRegister_AsRegister(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Register_getId(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyRegister_AsRegister(self)->getId());
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


      static PyObject* Register_richcompare(PyObject* self, PyObject* other, int op) {
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
        {"getId",             Register_getId,            METH_NOARGS,    ""},
        {"getName",           Register_getName,          METH_NOARGS,    ""},
        {"getSize",           Register_getSize,          METH_NOARGS,    ""},
        {"getType",           Register_getType,          METH_NOARGS,    ""},
        {"isOverlapWith",     Register_isOverlapWith,    METH_O,         ""},
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

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
