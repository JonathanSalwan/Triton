//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/peHeader.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_PeHeader_page PeHeader
    \brief [**python api**] All information about the PeHeader python object.

\tableofcontents

\section py_PeHeader_description Description
<hr>

This object is used to represent the main Header from the PE binary format.

\subsection py_PeHeader_example Example

~~~~~~~~~~~~~{.py}
>>> b = PE('C:/Windows/System32/notepad.exe')

>>> hex(b.getHeader().getEntry())
'0x45bc40L'
~~~~~~~~~~~~~

\section PeHeader_py_api Python API - Methods of the PeHeader class
<hr>

- <b>integer getEntry(void)</b><br>
Returns the entry point. This member gives the virtual address to which the system
first transfers control, thus starting the process. If the file has no associated
entry point, this member holds zero.

- <b>\ref py_PE_page getMachine(void)</b><br>
Returns the machine. This member specifies the required architecture for an individual file.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PeHeader destructor.
      void PeHeader_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPeHeader_AsPeHeader(self);
        Py_DECREF(self);
      }


      static PyObject* PeHeader_getEntry(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPeHeader_AsPeHeader(self)->getOptionalHeader().getAddressOfEntryPoint());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeHeader_getMachine(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyPeHeader_AsPeHeader(self)->getFileHeader().getMachine());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! PeHeader methods.
      PyMethodDef PeHeader_callbacks[] = {
        {"getEntry",      PeHeader_getEntry,          METH_NOARGS,    ""},
        {"getMachine",    PeHeader_getMachine,        METH_NOARGS,    ""},
        {nullptr,         nullptr,                    0,              nullptr}
      };


      PyTypeObject PeHeader_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PeHeader",                                 /* tp_name */
        sizeof(PeHeader_Object),                    /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PeHeader_dealloc,               /* tp_dealloc */
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
        "PeHeader objects",                         /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PeHeader_callbacks,                         /* tp_methods */
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


      PyObject* PyPeHeader(const triton::format::pe::PeHeader& header) {
        PeHeader_Object* object;

        PyType_Ready(&PeHeader_Type);
        object = PyObject_NEW(PeHeader_Object, &PeHeader_Type);
        if (object != NULL)
          object->header = new triton::format::pe::PeHeader(header);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
