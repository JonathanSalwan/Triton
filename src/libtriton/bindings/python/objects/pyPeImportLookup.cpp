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



/*! \page py_PeImportLookup_page PeImportLookup
    \brief [**python api**] All information about the PeImportLookup python object.

\tableofcontents

\section py_PeImportLookup_description Description
<hr>

This object is used to represent an import table from the PE binary format.

\subsection py_PeImportLookup_example Example

~~~~~~~~~~~~~{.py}
>>> b = Pe('C:/Windows/System32/notepad.exe')
>>> for tbl in b.getImportTable():
...     print tbl.getName(),":"
...     for lookup in tbl.getEntries():
...         print "    ",hex(lookup.getOrdinal())," - ",lookup.getName()
...
ADVAPI32.dll :
     0x214L  -  OpenProcessToken
     0x16fL  -  GetTokenInformation
     0xeeL  -  DuplicateEncryptionInfoFile
     0x2a6L  -  RegSetValueExW
     0x296L  -  RegQueryValueExW
     0x264L  -  RegCreateKeyW
     0x258L  -  RegCloseKey
     0x289L  -  RegOpenKeyExW
     0x121L  -  EventSetInformation
     0x120L  -  EventRegister
     0x122L  -  EventUnregister
     0x128L  -  EventWriteTransfer
     0x197L  -  IsTextUnicode
KERNEL32.dll :
...
~~~~~~~~~~~~~

\section PeImportLookup_py_api Python API - Methods of the PeImportLookup class
<hr>

- <b>string getName(void)</b><br>
Returns the name of the DLL the import table refers to.

- <b>int getOrdinal(void)</b><br>
If the lookup is by name, returns the ordinal hint. Otherwise it retuns the lookup ordinal.

- <b>bool importByName(void)</b><br>
Returns whether the lookup is by name, rather than by ordinal.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PeImportLookup destructor.
      void PeImportLookup_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPeImportLookup_AsPeImportLookup(self);
        Py_DECREF(self);
      }


      static PyObject* PeImportLookup_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPeImportLookup_AsPeImportLookup(self)->name.c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeImportLookup_getOrdinal(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyPeImportLookup_AsPeImportLookup(self)->ordinalNumber);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeImportLookup_importByName(PyObject* self, PyObject* noarg) {
        try {
          return PyBool_FromLong(PyPeImportLookup_AsPeImportLookup(self)->importByName);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! PeImportLookup methods.
      PyMethodDef PeImportLookup_callbacks[] = {
        {"getName" ,          PeImportLookup_getName,             METH_NOARGS,    ""},
        {"getOrdinal" ,       PeImportLookup_getOrdinal,          METH_NOARGS,    ""},
        {"importByName" ,     PeImportLookup_importByName,        METH_NOARGS,    ""},
        {nullptr,             nullptr,                            0,              nullptr}
      };


      PyTypeObject PeImportLookup_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PeImportLookup",                           /* tp_name */
        sizeof(PeImportLookup_Object),              /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PeImportLookup_dealloc,         /* tp_dealloc */
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
        "PeImportLookup objects",                   /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PeImportLookup_callbacks,                   /* tp_methods */
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


      PyObject* PyPeImportLookup(const triton::format::pe::PeImportLookup& impt) {
        PeImportLookup_Object* object;

        PyType_Ready(&PeImportLookup_Type);
        object = PyObject_NEW(PeImportLookup_Object, &PeImportLookup_Type);
        if (object != NULL)
          object->impt = new triton::format::pe::PeImportLookup(impt);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
