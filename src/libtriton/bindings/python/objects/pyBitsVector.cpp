//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/bitsVector.hpp>
#include <triton/exceptions.hpp>



/* setup doctest context

>>> from triton import ARCH, TritonContext, REG
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

*/

/*! \page py_BitsVector_page BitsVector
    \brief [**python api**] All information about the BitsVector python object.

\tableofcontents

\section py_BitsVector_description Description
<hr>

This object is used to represent a bits vector. Mainly used by \ref py_Register_page, \ref py_MemoryAccess_page and \ref py_Immediate_page.

~~~~~~~~~~~~~{.py}
>>> ah = ctxt.registers.ah
>>> bv = ah.getBitvector()
>>> bv.getHigh()
15L
>>> bv.getLow()
8L
>>> bv.getVectorSize()
8L
>>> bv.getMaxValue()
255L

~~~~~~~~~~~~~

\section BitsVector_py_api Python API - Methods of the BitsVector class
<hr>

- <b>integer getHigh(void)</b><br>
Returns the highest bit position.

- <b>integer getLow(void)</b><br>
Returns the lower bit position.

- <b>integer getMaxValue(void)</b><br>
Returns the max value of the vector.

- <b>integer getVectorSize(void)</b><br>
Returns the size of the vector.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! BitsVector destructor.
      void BitsVector_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyBitsVector_AsBitsVector(self);
        Py_DECREF(self);
      }


      static PyObject* BitsVector_getHigh(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyBitsVector_AsBitsVector(self)->getHigh());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BitsVector_getLow(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyBitsVector_AsBitsVector(self)->getLow());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BitsVector_getMaxValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyBitsVector_AsBitsVector(self)->getMaxValue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BitsVector_getVectorSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyBitsVector_AsBitsVector(self)->getVectorSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int BitsVector_print(PyObject* self) {
        triton::uint32 high = PyBitsVector_AsBitsVector(self)->getHigh();
        triton::uint32 low  = PyBitsVector_AsBitsVector(self)->getLow();
        std::cout << "bv[" << std::dec << high << ".." << low << "]";
        return 0;
      }


      static PyObject* BitsVector_str(PyObject* self) {
        try {
          triton::uint32 high = PyBitsVector_AsBitsVector(self)->getHigh();
          triton::uint32 low  = PyBitsVector_AsBitsVector(self)->getLow();
          return PyString_FromFormat("bv[%d..%d]", high, low);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! BitsVector methods.
      PyMethodDef BitsVector_callbacks[] = {
        {"getHigh",         BitsVector_getHigh,         METH_NOARGS,    ""},
        {"getLow",          BitsVector_getLow,          METH_NOARGS,    ""},
        {"getMaxValue",     BitsVector_getMaxValue,     METH_NOARGS,    ""},
        {"getVectorSize",   BitsVector_getVectorSize,   METH_NOARGS,    ""},
        {nullptr,           nullptr,                    0,              nullptr}
      };


      PyTypeObject BitsVector_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "BitsVector",                               /* tp_name */
        sizeof(BitsVector_Object),                  /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)BitsVector_dealloc,             /* tp_dealloc */
        (printfunc)BitsVector_print,                /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)BitsVector_str,                   /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "BitsVector objects",                       /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        BitsVector_callbacks,                       /* tp_methods */
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


      template PyObject* PyBitsVector(const triton::arch::Immediate& op);
      template PyObject* PyBitsVector(const triton::arch::MemoryAccess& op);
      template PyObject* PyBitsVector(const triton::arch::Register& op);
      template <typename T>
      PyObject* PyBitsVector(const T& op) {
        BitsVector_Object* object;

        PyType_Ready(&BitsVector_Type);
        object = PyObject_NEW(BitsVector_Object, &BitsVector_Type);
        if (object != NULL)
          object->bv = new triton::arch::BitsVector(op);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
