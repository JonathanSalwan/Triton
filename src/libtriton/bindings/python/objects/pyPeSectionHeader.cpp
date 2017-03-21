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



/*! \page py_PeSectionHeader_page PeSectionHeader
    \brief [**python api**] All information about the PeSectionHeader python object.

\tableofcontents

\section py_PeSectionHeader_description Description
<hr>

This object is used to represent a Section Header entry from the PE binary format.

\subsection py_PeSectionHeader_example Example

~~~~~~~~~~~~~{.py}
>>> b = Pe('C:/Windows/System32/notepad.exe')

>>> for section in b.getSectionHeaders():
...     print section.getName(), '\t', hex(section.getVirtualAddress())
...
.text   0x1000L
.data   0x1c000L
.idata  0x1f000L
.rsrc   0x22000L
.reloc  0x3c000L
~~~~~~~~~~~~~

\section PeSectionHeader_py_api Python API - Methods of the PeSectionHeader class
<hr>

- <b>bool getFlags(void)</b><br>
Returns the section flags. Sections support one-bit flags that describe miscellaneous attributes.
If a flag bit is set in triton::format::pe::PeSectionHeader::flags, the attribute is "on"
for the section. Otherwise, the attribute is "off" or does not apply. Undefined attributes are
set to zero.

- <b>string getName(void)</b><br>
Returns the section name. This member specifies the name of the section as string.<br>
e.g: `.text`

- <b>integer getRawAddress(void)</b><br>
Returns the section offset in the binary file. This member's value holds the byte offset from
the beginning of the file to the first byte in the section.

- <b>integer getRawSize(void)</b><br>
Returns the section size. This member holds the section's size in bytes. The section occupies sh_size bytes in the file.

- <b>integer getVirtualAddress(void)</b><br>
Returns the virtual section address. If this section appears in the memory image of a
process, this member holds the address at which the section's first byte should reside.
Otherwise, the member contains zero.

- <b>integer getVirtualSize(void)</b><br>
Returns the virtual section size.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PeSectionHeader destructor.
      void PeSectionHeader_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPeSectionHeader_AsPeSectionHeader(self);
        Py_DECREF(self);
      }


      static PyObject* PeSectionHeader_getVirtualAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPeSectionHeader_AsPeSectionHeader(self)->getVirtualAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeSectionHeader_getVirtualSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPeSectionHeader_AsPeSectionHeader(self)->getVirtualSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeSectionHeader_getRawAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPeSectionHeader_AsPeSectionHeader(self)->getRawAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeSectionHeader_getRawSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPeSectionHeader_AsPeSectionHeader(self)->getRawSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeSectionHeader_getFlags(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPeSectionHeader_AsPeSectionHeader(self)->getCharacteristics());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PeSectionHeader_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPeSectionHeader_AsPeSectionHeader(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! PeSectionHeader methods.
      PyMethodDef PeSectionHeader_callbacks[] = {
        {"getFlags",          PeSectionHeader_getFlags,          METH_NOARGS,    ""},
        {"getName" ,          PeSectionHeader_getName,           METH_NOARGS,    ""},
        {"getRawAddress",     PeSectionHeader_getRawAddress,     METH_NOARGS,    ""},
        {"getRawSize",        PeSectionHeader_getRawSize,        METH_NOARGS,    ""},
        {"getVirtualAddress", PeSectionHeader_getVirtualAddress, METH_NOARGS,    ""},
        {"getVirtualSize",    PeSectionHeader_getVirtualSize,    METH_NOARGS,    ""},
        {nullptr,             nullptr,                           0,              nullptr}
      };


      PyTypeObject PeSectionHeader_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PeSectionHeader",                          /* tp_name */
        sizeof(PeSectionHeader_Object),             /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PeSectionHeader_dealloc,        /* tp_dealloc */
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
        "PeSectionHeader objects",                  /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PeSectionHeader_callbacks,                  /* tp_methods */
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


      PyObject* PyPeSectionHeader(const triton::format::pe::PeSectionHeader& shdr) {
        PeSectionHeader_Object* object;

        PyType_Ready(&PeSectionHeader_Type);
        object = PyObject_NEW(PeSectionHeader_Object, &PeSectionHeader_Type);
        if (object != NULL)
          object->shdr = new triton::format::pe::PeSectionHeader(shdr);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
