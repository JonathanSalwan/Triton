//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <peHeader.hpp>
#include <exceptions.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>



/*! \page py_PESectionHeader_page PESectionHeader
    \brief [**python api**] All information about the PESectionHeader python object.

\tableofcontents

\section py_PESectionHeader_description Description
<hr>

This object is used to represent a Section Header entry from the PE binary format.

\subsection py_PESectionHeader_example Example

~~~~~~~~~~~~~{.py}
>>> b = PE('C:/Windows/System32/notepad.exe')

>>> for section in b.getSectionHeaders():
...     print section.getName(), '\t', hex(section.getAddr())
...
                0x0L
.interp         0x400270L
.note.ABI-tag   0x40028cL
.gnu.hash       0x4002b0L
.dynsym         0x40a388L
.dynstr         0x431268L
.gnu.version    0x451bc8L
.gnu.version_r  0x454fb0L
.rela.dyn       0x4550d0L
.rela.plt       0x455748L
.init           0x4580d0L
.plt            0x4580f0L
.text           0x459cb0L
.fini           0x783dccL
.rodata         0x783e00L
.eh_frame_hdr   0x961480L
.eh_frame       0x977898L
.init_array     0xbfdda0L
.fini_array     0xbfdda8L
.jcr            0xbfddb0L
.dynamic        0xbfddb8L
.got            0xbfdff8L
.got.plt        0xbfe000L
.data           0xbfee00L
.bss            0xc12280L
.shstrtab       0x0L
~~~~~~~~~~~~~

\section PESectionHeader_py_api Python API - Methods of the PESectionHeader class
<hr>

- <b>integer getVirtualAddress(void)</b><br>
Returns the virtual section address. If this section appears in the memory image of a
process, this member holds the address at which the section's first byte should reside.
Otherwise, the member contains zero.

- <b>integer getVirtualSize(void)</b><br>
Returns the virtual section size.

- <b>integer getRawAddress(void)</b><br>
Returns the section offset in the binary file. This member's value holds the byte offset from
the beginning of the file to the first byte in the section. 

- <b>integer getRawSize(void)</b><br>
Returns the section size. This member holds the section's size in bytes. The section occupies sh_size bytes in the file.

- <b>bool getFlags(void)</b><br>
Returns the section flags. Sections support one-bit flags that describe miscellaneous attributes.
If a flag bit is set in triton::format::pe::PESectionHeader::flags, the attribute is "on"
for the section. Otherwise, the attribute is "off" or does not apply. Undefined attributes are
set to zero.

- <b>string getName(void)</b><br>
Returns the section name. This member specifies the name of the section as string.<br>
e.g: `.text`

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! PESectionHeader destructor.
      void PESectionHeader_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyPESectionHeader_AsPESectionHeader(self);
        Py_DECREF(self);
      }


      static PyObject* PESectionHeader_getVirtualAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPESectionHeader_AsPESectionHeader(self)->virtualAddress);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PESectionHeader_getVirtualSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPESectionHeader_AsPESectionHeader(self)->virtualSize);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PESectionHeader_getRawAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPESectionHeader_AsPESectionHeader(self)->rawAddress);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PESectionHeader_getRawSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPESectionHeader_AsPESectionHeader(self)->rawSize);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PESectionHeader_getFlags(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyPESectionHeader_AsPESectionHeader(self)->characteristics);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* PESectionHeader_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString((char*)PyPESectionHeader_AsPESectionHeader(self)->name);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfSectionHeader methods.
      PyMethodDef PESectionHeader_callbacks[] = {
        {"getVirtualAddress", PESectionHeader_getVirtualAddress, METH_NOARGS,    ""},
        {"getVirtualSize",    PESectionHeader_getVirtualSize,    METH_NOARGS,    ""},
        {"getRawAddress",     PESectionHeader_getRawAddress,     METH_NOARGS,    ""},
        {"getRawSize",        PESectionHeader_getRawSize,        METH_NOARGS,    ""},
        {"getFlags",          PESectionHeader_getFlags,          METH_NOARGS,    ""},
        {"getName" ,          PESectionHeader_getName,           METH_NOARGS,    ""},
        {nullptr,             nullptr,                           0,              nullptr}
      };


      PyTypeObject PESectionHeader_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "PESectionHeader",                          /* tp_name */
        sizeof(PESectionHeader_Object),             /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)PESectionHeader_dealloc,        /* tp_dealloc */
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
        "PESectionHeader objects",                  /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        PESectionHeader_callbacks,                  /* tp_methods */
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


      PyObject* PyPESectionHeader(const triton::format::pe::PESectionHeader& shdr) {
        PESectionHeader_Object* object;

        PyType_Ready(&PESectionHeader_Type);
        object = PyObject_NEW(PESectionHeader_Object, &PESectionHeader_Type);
        if (object != NULL)
          object->shdr = new triton::format::pe::PESectionHeader(shdr);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
