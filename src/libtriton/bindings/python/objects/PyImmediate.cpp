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



/*! \page py_Immediate_page Immediate
    \brief [**python api**] All information about the Immediate python object.

\tableofcontents

\section py_Immediate_description Description
<hr>

This object is used to represent an Immediate.

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

- **getBitSize(void)**<br>
Returns the immediate's size in bits as integer.<br>
e.g: `64`

- **getBitvector(void)**<br>
Returns the bitvector as \ref py_Bitvector_page.

- **getSize(void)**<br>
Returns immediate's size in bytes as integer.<br>
e.g: `8`

- **getType(void)**<br>
Returns immediate's type in bytes as \ref py_OPERAND_page.<br>

- **getValue(void)**<br>
Returns the immediate's value.

- **setValue(void)**<br>
Sets the immediate's value.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Immediate's Destructor.
      void ImmediateOperand_dealloc(PyObject* self) {
        delete PyImmediateOperand_AsImmediateOperand(self);
        Py_DECREF(self);
      }


      static PyObject* ImmediateOperand_getBitvector(PyObject* self, PyObject* noarg) {
        return PyBitvector(*PyImmediateOperand_AsImmediateOperand(self));
      }


      static PyObject* ImmediateOperand_getBitSize(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyImmediateOperand_AsImmediateOperand(self)->getBitSize());
      }


      static PyObject* ImmediateOperand_getSize(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyImmediateOperand_AsImmediateOperand(self)->getSize());
      }


      static PyObject* ImmediateOperand_getType(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PyImmediateOperand_AsImmediateOperand(self)->getType());
      }


      static PyObject* ImmediateOperand_getValue(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint(PyImmediateOperand_AsImmediateOperand(self)->getValue());
      }


      static PyObject* ImmediateOperand_setValue(PyObject* self, PyObject* value) {
        if (!PyLong_Check(value) && !PyInt_Check(value))
          return PyErr_Format(PyExc_TypeError, "setValue(): expected an integer as argument");
        PyImmediateOperand_AsImmediateOperand(self)->setValue(PyLong_AsUint(value));
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* Immediate_str(ImmediateOperand_Object *obj) {
        std::stringstream str;
        str << *(obj->imm);
        return PyString_FromFormat("%s", str.str().c_str());
      }


      //! Immediate's methods.
      PyMethodDef ImmediateOperand_callbacks[] = {
        {"getBitSize",    ImmediateOperand_getBitSize,     METH_NOARGS,     ""},
        {"getBitvector",  ImmediateOperand_getBitvector,   METH_NOARGS,     ""},
        {"getSize",       ImmediateOperand_getSize,        METH_NOARGS,     ""},
        {"getType",       ImmediateOperand_getType,        METH_NOARGS,     ""},
        {"getValue",      ImmediateOperand_getValue,       METH_NOARGS,     ""},
        {"setValue",      ImmediateOperand_setValue,       METH_O,          ""},
        {nullptr,         nullptr,                         0,               nullptr}
      };


      PyTypeObject ImmediateOperand_Type = {
          PyObject_HEAD_INIT(&PyType_Type)
          0,                                          /* ob_size*/
          "Immediate",                                /* tp_name*/
          sizeof(ImmediateOperand_Object),            /* tp_basicsize*/
          0,                                          /* tp_itemsize*/
          (destructor)ImmediateOperand_dealloc,       /* tp_dealloc*/
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
          (reprfunc)Immediate_str,                    /* tp_str*/
          0,                                          /* tp_getattro*/
          0,                                          /* tp_setattro*/
          0,                                          /* tp_as_buffer*/
          Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
          "Immediate objects",                        /* tp_doc */
          0,                                          /* tp_traverse */
          0,                                          /* tp_clear */
          0,                                          /* tp_richcompare */
          0,                                          /* tp_weaklistoffset */
          0,                                          /* tp_iter */
          0,                                          /* tp_iternext */
          ImmediateOperand_callbacks,                 /* tp_methods */
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


      PyObject* PyImmediateOperand(triton::arch::ImmediateOperand &imm) {
        ImmediateOperand_Object *object;

        PyType_Ready(&ImmediateOperand_Type);
        object = PyObject_NEW(ImmediateOperand_Object, &ImmediateOperand_Type);
        if (object != NULL)
          object->imm = new triton::arch::ImmediateOperand(imm);

        return (PyObject* )object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
