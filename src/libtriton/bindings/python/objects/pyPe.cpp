//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/pe.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_Pe_page Pe
    \brief [**python api**] All information about the Pe python object.

\tableofcontents

\section py_Pe_description Description
<hr>

This object is used to represent the PE binary format.

\subsection py_Pe_example Example

~~~~~~~~~~~~~{.py}
>>> b = Pe('C:/Windows/System32/notepad.exe')

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

\subsection py_Pe_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> binary = Pe('C:/Windows/System32/notepad.exe')
~~~~~~~~~~~~~

\section Pe_py_api Python API - Methods of the Pe class
<hr>

- <b>[\ref py_PeExportTable_page, ...] getExportTable(void)</b><br>
Returns the list of export table entries.

- <b>\ref py_PeHeader_page getHeader(void)</b><br>
Returns the PE header.

- <b>[\ref py_PeImportTable_page, ...] getImportTable(void)</b><br>
Returns the list of import table entries.

- <b>string getPath(void)</b><br>
Returns the path of the parsed binary.<br>
e.g: `C:/Windows/System32/notepad.exe`

- <b>bytes getRaw(void)</b><br>
Returns the raw binary.

- <b>[\ref py_PeSectionHeader_page, ...] getSectionHeaders(void)</b><br>
Returns the list of section headers.

- <b>[string, ...] getSharedLibraries(void)</b><br>
Returns the list of shared library dependencies.<br>
e.g: `["ADVAPI32.dll", "KERNEL32.dll", "GDI32.dll", ...]`

- <b>integer getSize(void)</b><br>
Returns the binary size.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Pe destructor.
      void Pe_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPe_AsPe(self);
        Py_DECREF(self);
      }


      static PyObject* Pe_getHeader(PyObject* self, PyObject* noarg) {
        try {
          return PyPeHeader(PyPe_AsPe(self)->getHeader());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Pe_getPath(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString(PyPe_AsPe(self)->getPath().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Pe_getRaw(PyObject* self, PyObject* noarg) {
        try {
          const triton::uint8* raw = PyPe_AsPe(self)->getRaw();
          triton::usize size       = PyPe_AsPe(self)->getSize();
          return PyBytes_FromStringAndSize(reinterpret_cast<const char*>(raw), size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Pe_getSectionHeaders(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::pe::PeSectionHeader>& shdr = PyPe_AsPe(self)->getHeader().getSectionHeaders();
          ret = xPyList_New(shdr.size());
          for (triton::uint32 i = 0; i < shdr.size(); i++) {
            PyList_SetItem(ret, i, PyPeSectionHeader(shdr[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* Pe_getSharedLibraries(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<std::string>& lib = PyPe_AsPe(self)->getSharedLibraries();
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


      static PyObject* Pe_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUsize(PyPe_AsPe(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Pe_getImportTable(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::pe::PeImportDirectory>& sym = PyPe_AsPe(self)->getImportTable();
          ret = xPyList_New(sym.size());
          for (triton::uint32 i = 0; i < sym.size(); i++) {
            PyList_SetItem(ret, i, PyPeImportTable(sym[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* Pe_getExportTable(PyObject* self, PyObject* noarg) {
        try {
          return PyPeExportTable(PyPe_AsPe(self)->getExportTable());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! Pe methods.
      PyMethodDef Pe_callbacks[] = {
        {"getExportTable",        Pe_getExportTable,       METH_NOARGS,     ""},
        {"getHeader",             Pe_getHeader,            METH_NOARGS,     ""},
        {"getImportTable",        Pe_getImportTable,       METH_NOARGS,     ""},
        {"getPath",               Pe_getPath,              METH_NOARGS,     ""},
        {"getRaw",                Pe_getRaw,               METH_NOARGS,     ""},
        {"getSectionHeaders",     Pe_getSectionHeaders,    METH_NOARGS,     ""},
        {"getSharedLibraries",    Pe_getSharedLibraries,   METH_NOARGS,     ""},
        {"getSize",               Pe_getSize,              METH_NOARGS,     ""},
        {nullptr,                 nullptr,                  0,              nullptr}
      };


      PyTypeObject Pe_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Pe",                                       /* tp_name */
        sizeof(Pe_Object),                          /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Pe_dealloc,                     /* tp_dealloc */
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
        "Pe objects",                               /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Pe_callbacks,                               /* tp_methods */
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


      PyObject* PyPe(const std::string& path) {
        Pe_Object* object;

        PyType_Ready(&Pe_Type);
        object = PyObject_NEW(Pe_Object, &Pe_Type);
        if (object != NULL)
          object->pe = new triton::format::pe::Pe(path);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
