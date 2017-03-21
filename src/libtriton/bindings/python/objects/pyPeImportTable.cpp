//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/peImportDirectory.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_PeImportTable_page PeImportTable
    \brief [**python api**] All information about the PeImportTable python object.

\tableofcontents

\section py_PeImportTable_description Description
<hr>

This object is used to represent an import table from the PE binary format.

\subsection py_PeImportTable_example Example

~~~~~~~~~~~~~{.py}
>>> b = Pe('C:/Windows/System32/notepad.exe')

>>> for tbl in b.getImportTable():
...     print tbl.getName()
...
ADVAPI32.dll
KERNEL32.dll
GDI32.dll
USER32.dll
msvcrt.dll
api-ms-win-core-com-l1-1-1.dll
OLEAUT32.dll
api-ms-win-core-synch-l1-2-0.dll
api-ms-win-core-errorhandling-l1-1-1.dll
api-ms-win-core-processthreads-l1-1-2.dll
api-ms-win-core-libraryloader-l1-2-0.dll
api-ms-win-core-profile-l1-1-0.dll
api-ms-win-core-sysinfo-l1-2-1.dll
api-ms-win-core-heap-l1-2-0.dll
api-ms-win-core-winrt-string-l1-1-0.dll
api-ms-win-core-winrt-error-l1-1-1.dll
api-ms-win-core-string-l1-1-0.dll
api-ms-win-core-winrt-l1-1-0.dll
api-ms-win-core-debug-l1-1-1.dll
COMCTL32.dll
COMDLG32.dll
FeClient.dll
ntdll.dll
PROPSYS.dll
SHELL32.dll
SHLWAPI.dll
WINSPOOL.DRV
urlmon.dll
~~~~~~~~~~~~~

\section PeImportTable_py_api Python API - Methods of the PeImportTable class
<hr>

- <b>[\ref py_PeImportLookup_page, ...] getEntries(void)</b><br>
Returns the entries in the import table.

- <b>string getName(void)</b><br>
Returns the name of the DLL the import table refers to.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PeImportTable destructor.
      void PeImportTable_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPeImportTable_AsPeImportDirectory(self);
        Py_DECREF(self);
      }


      static PyObject* PeImportTable_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPeImportTable_AsPeImportDirectory(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeImportTable_getEntries(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::pe::PeImportLookup>& sym = PyPeImportTable_AsPeImportDirectory(self)->getEntries();
          ret = xPyList_New(sym.size());
          for (triton::uint32 i = 0; i < sym.size(); i++) {
            PyList_SetItem(ret, i, PyPeImportLookup(sym[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      //! PeImportTable methods.
      PyMethodDef PeImportTable_callbacks[] = {
        {"getEntries" ,       PeImportTable_getEntries,          METH_NOARGS,    ""},
        {"getName" ,          PeImportTable_getName,             METH_NOARGS,    ""},
        {nullptr,             nullptr,                           0,              nullptr}
      };


      PyTypeObject PeImportTable_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PeImportTable",                            /* tp_name */
        sizeof(PeImportTable_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PeImportTable_dealloc,          /* tp_dealloc */
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
        "PeImportTable objects",                    /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PeImportTable_callbacks,                    /* tp_methods */
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


      PyObject* PyPeImportTable(const triton::format::pe::PeImportDirectory& impt) {
        PeImportTable_Object* object;

        PyType_Ready(&PeImportTable_Type);
        object = PyObject_NEW(PeImportTable_Object, &PeImportTable_Type);
        if (object != NULL)
          object->impt = new triton::format::pe::PeImportDirectory(impt);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
