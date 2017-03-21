//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/immediate.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_Immediate_page Immediate
    \brief [**python api**] All information about the Immediate python object.

\tableofcontents

\section py_Immediate_description Description
<hr>

This object is used to represent an immediate.

\subsection py_Immediate_example Example

~~~~~~~~~~~~~{.py}
>>> processing(inst)
>>> print inst
40000: mov eax, 0x14

>>> op1 = inst.getOperands()[1]
>>> print op1
0x14:32 bv[31..0]

>>> print hex(op1.getValue())
0x14L

>>> print op1.getBitSize()
32
~~~~~~~~~~~~~

\subsection py_Immediate_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> imm = Immediate(0x1234, CPUSIZE.WORD)
>>> print imm
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

- <b>\ref py_Bitvector_page getBitvector(void)</b><br>
Returns the bitvector.

- <b>integer getSize(void)</b><br>
Returns the size (in bytes) of the immediate.<br>
e.g: `8`

- <b>\ref py_OPERAND_page getType(void)</b><br>
Returns the type of the immediate. In this case this function returns `OPERAND.IMM`.

- <b>integer getValue(void)</b><br>
Returns the immediate value.

- <b>setValue(integer value)</b><br>
Sets the immediate value.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Immediate destructor.
      void Immediate_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyImmediate_AsImmediate(self);
        Py_DECREF(self);
      }


      static PyObject* Immediate_getBitvector(PyObject* self, PyObject* noarg) {
        try {
          return PyBitvector(*PyImmediate_AsImmediate(self));
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


      static PyObject* Immediate_setValue(PyObject* self, PyObject* value) {
        try {
          if (!PyLong_Check(value) && !PyInt_Check(value))
            return PyErr_Format(PyExc_TypeError, "setValue(): expected an integer as argument");
          PyImmediate_AsImmediate(self)->setValue(PyLong_AsUint64(value));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int Immediate_print(PyObject* self) {
        std::cout << PyImmediate_AsImmediate(self);
        return 0;
      }


      static PyObject* Immediate_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyImmediate_AsImmediate(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Immediate methods.
      PyMethodDef Immediate_callbacks[] = {
        {"getBitSize",    Immediate_getBitSize,     METH_NOARGS,     ""},
        {"getBitvector",  Immediate_getBitvector,   METH_NOARGS,     ""},
        {"getSize",       Immediate_getSize,        METH_NOARGS,     ""},
        {"getType",       Immediate_getType,        METH_NOARGS,     ""},
        {"getValue",      Immediate_getValue,       METH_NOARGS,     ""},
        {"setValue",      Immediate_setValue,       METH_O,          ""},
        {nullptr,         nullptr,                  0,               nullptr}
      };


      PyTypeObject Immediate_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Immediate",                                /* tp_name */
        sizeof(Immediate_Object),                   /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Immediate_dealloc,              /* tp_dealloc */
        (printfunc)Immediate_print,                 /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
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
        0                                           /* tp_version_tag */
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
