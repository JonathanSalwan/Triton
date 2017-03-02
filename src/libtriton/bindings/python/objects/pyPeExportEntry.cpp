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



/*! \page py_PeExportEntry_page PeExportEntry
    \brief [**python api**] All information about the PeExportEntry python object.

\tableofcontents

\section py_PeExportEntry_description Description
<hr>

This object is used to represent an exported symbol from the PE binary format.

\subsection py_PeExportEntry_example Example

~~~~~~~~~~~~~{.py}
>>> b = Pe('C:/Windows/System32/kernel32.dll')
>>> tbl = b.getExportTable()
>>> for entry in tbl.getEntries():
...     print "    ",hex(entry.getOrdinal())," - ",entry.getName(),
...     if entry.isForward():
...         print "->",entry.getForwarderName(),
...     print
...
     0x0L  -  BaseThreadInitThunk
     0x1L  -  InterlockedPushListSList -> NTDLL.RtlInterlockedPushListSList
     0x2L  -  Wow64Transition
     0x3L  -  AcquireSRWLockExclusive -> NTDLL.RtlAcquireSRWLockExclusive
     0x4L  -  AcquireSRWLockShared -> NTDLL.RtlAcquireSRWLockShared
     0x5L  -  ActivateActCtx
     0x6L  -  ActivateActCtxWorker
...
~~~~~~~~~~~~~

\section PeExportEntry_py_api Python API - Methods of the PeExportEntry class
<hr>

- <b>string getForwarderName(void)</b><br>
If the entry is a forwarder reference, returns the name of the target function.

- <b>string getName(void)</b><br>
Returns the name of the exported function.

- <b>int getOrdinal(void)</b><br>
Returns the ordinal number of the exported function.

- <b>bool isForward(void)</b><br>
Returns whether the lookup is a forwarder reference to another function.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PeExportEntry destructor.
      void PeExportEntry_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPeExportEntry_AsPeExportEntry(self);
        Py_DECREF(self);
      }


      static PyObject* PeExportEntry_isForward(PyObject* self, PyObject* noarg) {
        try {
          return PyBool_FromLong(PyPeExportEntry_AsPeExportEntry(self)->isForward);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeExportEntry_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPeExportEntry_AsPeExportEntry(self)->exportName.c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeExportEntry_getOrdinal(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyPeExportEntry_AsPeExportEntry(self)->ordinal);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeExportEntry_getForwarderName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPeExportEntry_AsPeExportEntry(self)->forwarderName.c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! PeExportEntry methods.
      PyMethodDef PeExportEntry_callbacks[] = {
        {"getForwarderName" , PeExportEntry_getForwarderName,    METH_NOARGS,    ""},
        {"getName" ,          PeExportEntry_getName,             METH_NOARGS,    ""},
        {"getOrdinal" ,       PeExportEntry_getOrdinal,          METH_NOARGS,    ""},
        {"isForward" ,        PeExportEntry_isForward,           METH_NOARGS,    ""},
        {nullptr,             nullptr,                           0,              nullptr}
      };


      PyTypeObject PeExportEntry_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PeExportEntry",                            /* tp_name */
        sizeof(PeExportEntry_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PeExportEntry_dealloc,          /* tp_dealloc */
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
        "PeExportEntry objects",                    /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PeExportEntry_callbacks,                    /* tp_methods */
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


      PyObject* PyPeExportEntry(const triton::format::pe::PeExportEntry& impt) {
        PeExportEntry_Object* object;

        PyType_Ready(&PeExportEntry_Type);
        object = PyObject_NEW(PeExportEntry_Object, &PeExportEntry_Type);
        if (object != NULL)
          object->impt = new triton::format::pe::PeExportEntry(impt);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
