//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfDynamicTable.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_ElfDynamicTable_page ElfDynamicTable
    \brief [**python api**] All information about the ElfDynamicTable python object.

\tableofcontents

\section py_ElfDynamicTable_description Description
<hr>

This object is used to represent the Dynamic Table from the ELF binary format.

\section ElfDynamicTable_py_api Python API - Methods of the ElfDynamicTable class
<hr>

- <b>\ref py_ELF_page getTag(void)</b><br>
Returns the tag of the dynamic entry. This member describes the kind of the entry.<br>
e.g: `DT_STRTAB`

- <b>integer getValue(void)</b><br>
Returns the value of the dynamic entry. This member represents integer values with various interpretations.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! ElfDynamicTable destructor.
      void ElfDynamicTable_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElfDynamicTable_AsElfDynamicTable(self);
        Py_DECREF(self);
      }


      static PyObject* ElfDynamicTable_getTag(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfDynamicTable_AsElfDynamicTable(self)->getTag());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfDynamicTable_getValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfDynamicTable_AsElfDynamicTable(self)->getValue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfDynamicTable methods.
      PyMethodDef ElfDynamicTable_callbacks[] = {
        {"getTag",      ElfDynamicTable_getTag,     METH_NOARGS,     ""},
        {"getValue",    ElfDynamicTable_getValue,   METH_NOARGS,     ""},
        {nullptr,       nullptr,                    0,               nullptr}
      };


      PyTypeObject ElfDynamicTable_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "ElfDynamicTable",                          /* tp_name */
        sizeof(ElfDynamicTable_Object),             /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)ElfDynamicTable_dealloc,        /* tp_dealloc */
        0,                                          /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        0,                                          /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "ElfDynamicTable objects",                  /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        ElfDynamicTable_callbacks,                  /* tp_methods */
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


      PyObject* PyElfDynamicTable(const triton::format::elf::ElfDynamicTable& dyn) {
        ElfDynamicTable_Object* object;

        PyType_Ready(&ElfDynamicTable_Type);
        object = PyObject_NEW(ElfDynamicTable_Object, &ElfDynamicTable_Type);
        if (object != NULL)
          object->dyn = new triton::format::elf::ElfDynamicTable(dyn);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
