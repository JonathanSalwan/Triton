//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/bitsVector.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_Bitvector_page Bitvector
    \brief [**python api**] All information about the Bitvector python object.

\tableofcontents

\section py_Bitvector_description Description
<hr>

This object is used to represent a bitvector. Mainly used by \ref py_Register_page and \ref py_MemoryAccess_page.

~~~~~~~~~~~~~{.py}
>>> ah = REG.AH
>>> bitvector = ah.getBitvector()
>>> bitvector.getHigh()
15
>>> bitvector.getLow()
8
>>> bitvector.getVectorSize()
8
~~~~~~~~~~~~~

\section Bitvector_py_api Python API - Methods of the Bitvector class
<hr>

- <b>integer getHigh(void)</b><br>
Returns the highest bit position.

- <b>integer getLow(void)</b><br>
Returns the lower bit position.

- <b>integer getVectorSize(void)</b><br>
Returns the size of the vector.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Bitvector destructor.
      void Bitvector_dealloc(PyObject* self) {
        std::cout << std::flush;
        Py_DECREF(self);
      }

      static PyObject* Bitvector_getHigh(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyBitvector_AsHigh(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Bitvector_getLow(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyBitvector_AsLow(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Bitvector_getVectorSize(PyObject* self, PyObject* noarg) {
        try {
          triton::uint32 vectorSize = ((PyBitvector_AsHigh(self) - PyBitvector_AsLow(self)) + 1);
          return PyLong_FromUint32(vectorSize);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int Bitvector_print(PyObject* self) {
        std::cout << "bv[" << std::dec << PyBitvector_AsHigh(self) << ".." << PyBitvector_AsLow(self) << "]";
        return 0;
      }


      static PyObject* Bitvector_str(PyObject* self) {
        try {
          return PyString_FromFormat("bv[%d..%d]", PyBitvector_AsHigh(self), PyBitvector_AsLow(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Bitvector methods.
      PyMethodDef Bitvector_callbacks[] = {
        {"getHigh",       Bitvector_getHigh,        METH_NOARGS,     ""},
        {"getLow",        Bitvector_getLow,         METH_NOARGS,     ""},
        {"getVectorSize", Bitvector_getVectorSize,  METH_NOARGS,     ""},
        {nullptr,         nullptr,                  0,               nullptr}
      };


      PyTypeObject Bitvector_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Bitvector",                                /* tp_name */
        sizeof(Bitvector_Object),                   /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Bitvector_dealloc,              /* tp_dealloc */
        (printfunc)Bitvector_print,                 /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)Bitvector_str,                    /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "Bitvector objects",                        /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Bitvector_callbacks,                        /* tp_methods */
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


      PyObject* PyBitvector(const triton::arch::Immediate& imm) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = imm.getHigh();
          object->low  = imm.getLow();
        }

        return (PyObject*)object;
      }


      PyObject* PyBitvector(const triton::arch::MemoryAccess& mem) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = mem.getHigh();
          object->low  = mem.getLow();
        }

        return (PyObject*)object;
      }


      PyObject* PyBitvector(const triton::arch::Register& reg) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = reg.getHigh();
          object->low  = reg.getLow();
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
