//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <pe.hpp>
#include <exceptions.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>



/*! \page py_PE_page PE
    \brief [**python api**] All information about the PE python object.

\tableofcontents

\section py_PE_description Description
<hr>

This object is used to represent the PE binary format.

\subsection py_PE_example Example

~~~~~~~~~~~~~{.py}
>>> b = PE('C:/Windows/System32/notepad.exe')

>>> for lib in b.getSharedLibraries():
...     print lib
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

>>> hex(b.getHeader().getEntry())
'0x1a410L'

>>> for section in b.getSectionHeaders():
...     print section.getName(), '\t', hex(section.getVirtualAddress())
...
.text   0x1000L
.data   0x1c000L
.idata  0x1f000L
.rsrc   0x22000L
.reloc  0x3c000L
~~~~~~~~~~~~~

\subsection py_PE_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> binary = PE('C:/Windows/System32/notepad.exe')
~~~~~~~~~~~~~

\section PE_py_api Python API - Methods of the PE class
<hr>

- <b>\ref py_PEHeader_page getHeader(void)</b><br>
Returns the PE header.

- <b>string getPath(void)</b><br>
Returns the path of the parsed binary.<br>
e.g: `C:/Windows/System32/notepad.exe`

- <b>bytes getRaw(void)</b><br>
Returns the raw binary.

- <b>[\ref py_PESectionHeader_page, ...] getSectionHeaders(void)</b><br>
Returns the list of section headers.

- <b>[string, ...] getSharedLibraries(void)</b><br>
Returns the list of shared library dependencies.<br>
e.g: `['ADVAPI32.dll', 'KERNEL32.dll', 'GDI32.dll', ....... ]`

- <b>integer getSize(void)</b><br>
Returns the binary size.

- <b>[\ref py_PEImportTable_page, ...] getImportTable(void)</b><br>
Returns the list of import table entries.

- <b>[\ref py_PEExportTable_page, ...] getExportTable(void)</b><br>
Returns the list of export table entries.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PE destructor.
      void PE_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPE_AsPE(self);
        Py_DECREF(self);
      }


      static PyObject* PE_getHeader(PyObject* self, PyObject* noarg) {
        try {
          return PyPEHeader(PyPE_AsPE(self)->getHeader());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PE_getPath(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString(PyPE_AsPE(self)->getPath().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PE_getRaw(PyObject* self, PyObject* noarg) {
        try {
          const triton::uint8* raw = PyPE_AsPE(self)->getRaw();
          triton::usize size       = PyPE_AsPE(self)->getSize();
          return PyBytes_FromStringAndSize(reinterpret_cast<const char*>(raw), size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PE_getSectionHeaders(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::pe::PESectionHeader>& shdr = PyPE_AsPE(self)->getHeader().getSectionHeaders();
          ret = xPyList_New(shdr.size());
          for (triton::uint32 i = 0; i < shdr.size(); i++) {
            PyList_SetItem(ret, i, PyPESectionHeader(shdr[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* PE_getSharedLibraries(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<std::string>& lib = PyPE_AsPE(self)->getSharedLibraries();
          ret = xPyList_New(lib.size());
          for (triton::uint32 i = 0; i < lib.size(); i++) {
            PyList_SetItem(ret, i, xPyString_FromString(lib[i].c_str()));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* PE_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUsize(PyPE_AsPE(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PE_getImportTable(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /*try {
          const std::vector<triton::format::pe::PEImportDirectory>& sym = PyPE_AsPE(self)->getImportTable();
          ret = xPyList_New(sym.size());
          for (triton::uint32 i = 0; i < sym.size(); i++) {
            PyList_SetItem(ret, i, PyPEImportTable(sym[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }*/

        return ret;
      }


      static PyObject* PE_getExportTable(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /*try {
          const std::vector<triton::format::pe::PEExportTable>& sym = PyPE_AsPE(self)->getExportTable();
          ret = xPyList_New(sym.size());
          for (triton::uint32 i = 0; i < sym.size(); i++) {
            PyList_SetItem(ret, i, PyPEExportTable(sym[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }*/

        return ret;
      }


      //! PE methods.
      PyMethodDef PE_callbacks[] = {
        {"getHeader",             PE_getHeader,            METH_NOARGS,     ""},
        {"getPath",               PE_getPath,              METH_NOARGS,     ""},
        {"getRaw",                PE_getRaw,               METH_NOARGS,     ""},
        {"getSectionHeaders",     PE_getSectionHeaders,    METH_NOARGS,     ""},
        {"getSharedLibraries",    PE_getSharedLibraries,   METH_NOARGS,     ""},
        {"getSize",               PE_getSize,              METH_NOARGS,     ""},
        {"getImportTable",        PE_getImportTable,       METH_NOARGS,     ""},
        {"getExportTable",        PE_getExportTable,       METH_NOARGS,     ""},
        {nullptr,                 nullptr,                  0,               nullptr}
      };


      PyTypeObject PE_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PE",                                       /* tp_name */
        sizeof(PE_Object),                          /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PE_dealloc,                     /* tp_dealloc */
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
        "PE objects",                               /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PE_callbacks,                               /* tp_methods */
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


      PyObject* PyPE(const std::string& path) {
        PE_Object* object;

        PyType_Ready(&PE_Type);
        object = PyObject_NEW(PE_Object, &PE_Type);
        if (object != NULL)
          object->pe = new triton::format::pe::PE(path);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
