//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/coreUtils.hpp>
#include <triton/exceptions.hpp>
#include <triton/immediate.hpp>

#include <iostream>



/* setup doctest context

>>> from __future__ import print_function
>>> from triton import TritonContext, ARCH, Instruction, Immediate, CPUSIZE

>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> inst = Instruction()
>>> inst.setOpcode(b"\xB8\x14\x00\x00\x00")

*/

/*! \page py_Immediate_page Immediate
    \brief [**python api**] All information about the Immediate Python object.

\tableofcontents

\section py_Immediate_description Description
<hr>

This object is used to represent an immediate.

\subsection py_Immediate_example Example

~~~~~~~~~~~~~{.py}
>>> ctxt.processing(inst)
0
>>> print(inst)
0x0: mov eax, 0x14

>>> op1 = inst.getOperands()[1]
>>> print(op1)
0x14:32 bv[31..0]

>>> print(hex(op1.getValue()))
0x14

>>> print(op1.getBitSize())
32

~~~~~~~~~~~~~

\subsection py_Immediate_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> imm = Immediate(0x1234, CPUSIZE.WORD)
>>> print(imm)
0x1234:16 bv[15..0]
>>> imm.getValue()
4660
>>> imm.getSize()
2
>>> imm.getBitSize()
16

~~~~~~~~~~~~~

\section Immediate_py_api Python API - Methods of the Immediate class
<hr>

- <b>integer getBitSize(void)</b><br>
Returns the size (in bits) of the immediate.<br>
e.g: `64`

- <b>\ref py_BitsVector_page getBitvector(void)</b><br>
Returns the bit vector.

- <b>\ref py_SHIFT_page getShiftType(void)</b><br>
Returns the shift type of the operand. Mainly used for AArch64.<br>
e.g: `SHIFT.ARM.LSL`

- <b>integer getShiftImmediate(void)</b><br>
Returns the shift immediate value of the operand. Mainly used for AArch64 and ARM32.<br>
e.g: `2`

- <b>\ref py_REG_page getShiftRegister(void)</b><br>
Returns the shift register of the operand. Mainly used for ARM32.<br>
e.g: `REG.ARM32.R0`

- <b>integer getSize(void)</b><br>
Returns the size (in bytes) of the immediate.<br>
e.g: `8`

- <b>\ref py_OPERAND_page getType(void)</b><br>
Returns the type of the immediate. In this case this function returns `OPERAND.IMM`.

- <b>integer getValue(void)</b><br>
Returns the immediate value.

- <b>void setValue(integer value, integer size)</b><br>
Sets the immediate value.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Immediate destructor.
      void Immediate_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyImmediate_AsImmediate(self);
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static PyObject* Immediate_getBitvector(PyObject* self, PyObject* noarg) {
        try {
          return PyBitsVector(*PyImmediate_AsImmediate(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getBitSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyImmediate_AsImmediate(self)->getBitSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getShiftType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyImmediate_AsImmediate(self)->getShiftType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getShiftImmediate(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyImmediate_AsImmediate(self)->getShiftImmediate());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getShiftRegister(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyImmediate_AsImmediate(self)->getShiftRegister());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyImmediate_AsImmediate(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyImmediate_AsImmediate(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_getValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyImmediate_AsImmediate(self)->getValue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Immediate_setValue(PyObject* self, PyObject* args) {
        PyObject* value = nullptr;
        PyObject* size  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &value, &size) == false) {
          return PyErr_Format(PyExc_TypeError, "Immediate::setValue(): Invalid number of arguments");
        }

        try {
          if (!PyLong_Check(value) && !PyInt_Check(value))
            return PyErr_Format(PyExc_TypeError, "Immediate::setValue(): expected an integer as first argument");

          if (!PyLong_Check(size) && !PyInt_Check(size))
            return PyErr_Format(PyExc_TypeError, "Immediate::setValue(): expected an integer as second argument");

          PyImmediate_AsImmediate(self)->setValue(PyLong_AsUint64(value), PyLong_AsUint32(size));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      #if !defined(IS_PY3_8) || !IS_PY3_8
      static int Immediate_print(PyObject* self, void* io, int s) {
        std::cout << PyImmediate_AsImmediate(self);
        return 0;
      }
      #endif


      static PyObject* Immediate_str(PyObject* self) {
        try {
          return PyStr_FromFormat("%s", triton::utils::toString(PyImmediate_AsImmediate(self)).c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Immediate methods.
      PyMethodDef Immediate_callbacks[] = {
        {"getBitSize",        Immediate_getBitSize,        METH_NOARGS,  ""},
        {"getBitvector",      Immediate_getBitvector,      METH_NOARGS,  ""},
        {"getShiftType",      Immediate_getShiftType,      METH_NOARGS,  ""},
        {"getShiftImmediate", Immediate_getShiftImmediate, METH_NOARGS,  ""},
        {"getShiftRegister",  Immediate_getShiftRegister,  METH_NOARGS,  ""},
        {"getSize",           Immediate_getSize,           METH_NOARGS,  ""},
        {"getType",           Immediate_getType,           METH_NOARGS,  ""},
        {"getValue",          Immediate_getValue,          METH_NOARGS,  ""},
        {"setValue",          Immediate_setValue,          METH_VARARGS, ""},
        {nullptr,             nullptr,                     0,            nullptr}
      };


      PyTypeObject Immediate_Type = {
        PyVarObject_HEAD_INIT(&PyType_Type, 0)
        "Immediate",                                /* tp_name */
        sizeof(Immediate_Object),                   /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Immediate_dealloc,              /* tp_dealloc */
        #if IS_PY3_8
        0,                                          /* tp_vectorcall_offset */
        #else
        (printfunc)Immediate_print,                 /* tp_print */
        #endif
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        (reprfunc)Immediate_str,                    /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)Immediate_str,                    /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "Immediate objects",                        /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Immediate_callbacks,                        /* tp_methods */
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
        #if IS_PY3
          0,                                        /* tp_version_tag */
          0,                                        /* tp_finalize */
          #if IS_PY3_8
            0,                                      /* tp_vectorcall */
            #if !IS_PY3_9
              0,                                    /* bpo-37250: kept for backwards compatibility in CPython 3.8 only */
            #endif
          #endif
        #else
          0                                         /* tp_version_tag */
        #endif
      };


      PyObject* PyImmediate(const triton::arch::Immediate& imm) {
        Immediate_Object* object;

        PyType_Ready(&Immediate_Type);
        object = PyObject_NEW(Immediate_Object, &Immediate_Type);
        if (object != NULL)
          object->imm = new triton::arch::Immediate(imm);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
