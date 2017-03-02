//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/peExportDirectory.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_PeExportTable_page PeExportTable
    \brief [**python api**] All information about the PeExportTable python object.

\tableofcontents

\section py_PeExportTable_description Description
<hr>

This object is used to represent an export table from the PE binary format.

\subsection py_PeExportTable_example Example

~~~~~~~~~~~~~{.py}
>>> b = Pe('C:/Windows/System32/kernel32.dll')
>>> print b.getExportTable().getName()
KERNEL32.dll
~~~~~~~~~~~~~

\section PeExportTable_py_api Python API - Methods of the PeExportTable class
<hr>

- <b>[\ref py_PeExportEntry_page, ...] getEntries(void)</b><br>
Returns the entries in the export table.

- <b>string getName(void)</b><br>
Returns the name of the DLL the export table refers to.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PeExportTable destructor.
      void PeExportTable_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPeExportTable_AsPeExportDirectory(self);
        Py_DECREF(self);
      }


      static PyObject* PeExportTable_getEntries(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::pe::PeExportEntry>& sym = PyPeExportTable_AsPeExportDirectory(self)->getEntries();
          ret = xPyList_New(sym.size());
          for (triton::uint32 i = 0; i < sym.size(); i++) {
            PyList_SetItem(ret, i, PyPeExportEntry(sym[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* PeExportTable_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPeExportTable_AsPeExportDirectory(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! PeExportTable methods.
      PyMethodDef PeExportTable_callbacks[] = {
        {"getEntries" ,       PeExportTable_getEntries,          METH_NOARGS,    ""},
        {"getName" ,          PeExportTable_getName,             METH_NOARGS,    ""},
        {nullptr,             nullptr,                           0,              nullptr}
      };


      PyTypeObject PeExportTable_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PeExportTable",                            /* tp_name */
        sizeof(PeExportTable_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PeExportTable_dealloc,          /* tp_dealloc */
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
        "PeExportTable objects",                    /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PeExportTable_callbacks,                    /* tp_methods */
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


      PyObject* PyPeExportTable(const triton::format::pe::PeExportDirectory& expt) {
        PeExportTable_Object* object;

        PyType_Ready(&PeExportTable_Type);
        object = PyObject_NEW(PeExportTable_Object, &PeExportTable_Type);
        if (object != NULL)
          object->expt = new triton::format::pe::PeExportDirectory(expt);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
