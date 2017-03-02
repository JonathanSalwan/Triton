//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfSectionHeader.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_ElfSectionHeader_page ElfSectionHeader
    \brief [**python api**] All information about the ElfSectionHeader python object.

\tableofcontents

\section py_ElfSectionHeader_description Description
<hr>

This object is used to represent a Section Header entry from the ELF binary format.

\subsection py_ElfSectionHeader_example Example

~~~~~~~~~~~~~{.py}
>>> b = Elf('/usr/bin/gdb')

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

\section ElfSectionHeader_py_api Python API - Methods of the ElfSectionHeader class
<hr>

- <b>integer getAddr(void)</b><br>
Returns the virtual section address. If this section appears in the memory image of a
process, this member holds the address at which the section's first byte should reside.
Otherwise, the member contains zero.

- <b>integer getAddralign(void)</b><br>
Returns the section alignement. Some sections have address alignment constraints. If a
section holds a doubleword, the system must ensure doubleword alignment for the entire
section. That is, the value of sh_addr must be congruent to zero, modulo the value of
triton::format::elf::ElfSectionHeader::addralign. Only zero and positive integral powers
of two are allowed. Values of zero or one mean the section has no alignment constraints.

- <b>integer getEntsize(void)</b><br>
Returns the size of an section entry. Some sections hold a table of fixed-sized entries,
such as a symbol table. For such a section, this member gives the size in bytes for each
entry. This member contains zero if the section does not hold a table of fixed-size entries.

- <b>bool getFlags(void)</b><br>
Returns the section flags. Sections support one-bit flags that describe miscellaneous attributes.
If a flag bit is set in triton::format::elf::ElfSectionHeader::flags, the attribute is "on"
for the section. Otherwise, the attribute is "off" or does not apply. Undefined attributes are
set to zero.

- <b>integer getIdxname(void)</b><br>
Returns the section index name. This member specifies the name of the section. Its value is an
index into the section header string table section, giving the location of a null-terminated
string.

- <b>\ref py_ELF_page getInfo(void)</b><br>
Returns the section info. This member holds extra information, whose interpretation depends
on the section type.

- <b>integer getLink(void)</b><br>
Returns the section link. This member holds a section header table index link, whose
interpretation depends on the section type.

- <b>string getName(void)</b><br>
Returns the section name. This member specifies the name of the section as string
based on the triton::format::elf::ElfSectionHeader::idxname.<br>
e.g: `.text`

- <b>integer getOffset(void)</b><br>
Returns the section offset in the binary file. This member's value holds the byte offset from
the beginning of the file to the first byte in the section. One section type, triton::format::elf::SHT_NOBITS,
occupies no space in the file, and its sh_offset member locates the conceptual placement in
thefile.

- <b>integer getSize(void)</b><br>
Returns the section size. This member holds the section's size in bytes. Unless the section
type is triton::format::elf::SHT_NOBITS, the section occupies sh_size bytes in the file. A
section of type triton::format::elf::SHT_NOBITS may have a nonzero size, but it occupies no
space in the file.

- <b>\ref py_ELF_page getType(void)</b><br>
Returns the section type. This member categorizes the section's contents and semantics.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! ElfSectionHeader destructor.
      void ElfSectionHeader_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElfSectionHeader_AsElfSectionHeader(self);
        Py_DECREF(self);
      }


      static PyObject* ElfSectionHeader_getAddr(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSectionHeader_AsElfSectionHeader(self)->getAddr());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getAddralign(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSectionHeader_AsElfSectionHeader(self)->getAddralign());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getEntsize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSectionHeader_AsElfSectionHeader(self)->getEntsize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getFlags(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSectionHeader_AsElfSectionHeader(self)->getFlags());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getIdxname(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSectionHeader_AsElfSectionHeader(self)->getIdxname());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getInfo(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSectionHeader_AsElfSectionHeader(self)->getInfo());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getLink(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSectionHeader_AsElfSectionHeader(self)->getLink());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString(PyElfSectionHeader_AsElfSectionHeader(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getOffset(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSectionHeader_AsElfSectionHeader(self)->getOffset());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSectionHeader_AsElfSectionHeader(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSectionHeader_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSectionHeader_AsElfSectionHeader(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfSectionHeader methods.
      PyMethodDef ElfSectionHeader_callbacks[] = {
        {"getAddr",       ElfSectionHeader_getAddr,       METH_NOARGS,    ""},
        {"getAddralign",  ElfSectionHeader_getAddralign,  METH_NOARGS,    ""},
        {"getEntsize",    ElfSectionHeader_getEntsize,    METH_NOARGS,    ""},
        {"getFlags",      ElfSectionHeader_getFlags,      METH_NOARGS,    ""},
        {"getIdxname",    ElfSectionHeader_getIdxname,    METH_NOARGS,    ""},
        {"getInfo",       ElfSectionHeader_getInfo,       METH_NOARGS,    ""},
        {"getLink",       ElfSectionHeader_getLink,       METH_NOARGS,    ""},
        {"getName",       ElfSectionHeader_getName,       METH_NOARGS,    ""},
        {"getOffset",     ElfSectionHeader_getOffset,     METH_NOARGS,    ""},
        {"getSize",       ElfSectionHeader_getSize,       METH_NOARGS,    ""},
        {"getType",       ElfSectionHeader_getType,       METH_NOARGS,    ""},
        {nullptr,         nullptr,                        0,              nullptr}
      };


      PyTypeObject ElfSectionHeader_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "ElfSectionHeader",                         /* tp_name */
        sizeof(ElfSectionHeader_Object),            /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)ElfSectionHeader_dealloc,       /* tp_dealloc */
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
        "ElfSectionHeader objects",                 /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        ElfSectionHeader_callbacks,                 /* tp_methods */
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


      PyObject* PyElfSectionHeader(const triton::format::elf::ElfSectionHeader& shdr) {
        ElfSectionHeader_Object* object;

        PyType_Ready(&ElfSectionHeader_Type);
        object = PyObject_NEW(ElfSectionHeader_Object, &ElfSectionHeader_Type);
        if (object != NULL)
          object->shdr = new triton::format::elf::ElfSectionHeader(shdr);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
