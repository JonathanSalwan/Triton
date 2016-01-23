//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <pythonObjects.hpp>
#include <pythonXFunctions.hpp>
#include <pythonUtils.hpp>



/*! \page py_Bitvector_page Bitvector
    \brief [**python api**] All information about the Bitvector python object.

\tableofcontents

\section py_Bitvector_description Description
<hr>

This object is used to represent a bitvector. Mainly used by \ref py_Register_page and \ref py_Memory_page.

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

- **getHigh(void)**<br>
Returns the highest bit position.

- **getLow(void)**<br>
Returns the lower bit position.

- **getVectorSize(void)**<br>
Returns the vector's size.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Bitvector's Destructor.
      void Bitvector_dealloc(PyObject* self) {
        Py_DECREF(self);
      }

      static PyObject* Bitvector_getHigh(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyBitvector_AsHigh(self));
      }


      static PyObject* Bitvector_getLow(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyBitvector_AsLow(self));
      }


      static PyObject* Bitvector_getVectorSize(PyObject* self, PyObject* noarg) {
        triton::uint32 vectorSize = ((PyBitvector_AsHigh(self) - PyBitvector_AsLow(self)) + 1);
        return Py_BuildValue("k", vectorSize);
      }


      static PyObject* Bitvector_str(Bitvector_Object* obj) {
        return PyString_FromFormat("bv[%d..%d]", obj->high, obj->low);
      }


      //! Bitvector's methods.
      PyMethodDef Bitvector_callbacks[] = {
        {"getHigh",       Bitvector_getHigh,        METH_NOARGS,     ""},
        {"getLow",        Bitvector_getLow,         METH_NOARGS,     ""},
        {"getVectorSize", Bitvector_getVectorSize,  METH_NOARGS,     ""},
        {nullptr,         nullptr,                  0,               nullptr}
      };


      PyTypeObject Bitvector_Type = {
          PyObject_HEAD_INIT(&PyType_Type)
          0,                                          /* ob_size*/
          "Bitvector",                                /* tp_name*/
          sizeof(Bitvector_Object),                   /* tp_basicsize*/
          0,                                          /* tp_itemsize*/
          (destructor)Bitvector_dealloc,              /* tp_dealloc*/
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
          (reprfunc)Bitvector_str,                    /* tp_str*/
          0,                                          /* tp_getattro*/
          0,                                          /* tp_setattro*/
          0,                                          /* tp_as_buffer*/
          Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
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
      };


      PyObject* PyBitvector(triton::arch::ImmediateOperand &imm) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = imm.getHigh();
          object->low  = imm.getLow();
        }

        return (PyObject*)object;
      }


      PyObject* PyBitvector(triton::arch::MemoryOperand &mem) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = mem.getHigh();
          object->low  = mem.getLow();
        }

        return (PyObject*)object;
      }


      PyObject* PyBitvector(triton::arch::RegisterOperand &reg) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = reg.getHigh();
          object->low  = reg.getLow();
        }

        return (PyObject*)object;
      }


      PyObject* PyBitvector(triton::uint32 high, triton::uint32 low) {
        Bitvector_Object* object;

        PyType_Ready(&Bitvector_Type);
        object = PyObject_NEW(Bitvector_Object, &Bitvector_Type);
        if (object != NULL) {
          object->high = high;
          object->low  = low;
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
