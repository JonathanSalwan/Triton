//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfHeader.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_ElfHeader_page ElfHeader
    \brief [**python api**] All information about the ElfHeader python object.

\tableofcontents

\section py_ElfHeader_description Description
<hr>

This object is used to represent the main Header from the ELF binary format.

\subsection py_ElfHeader_example Example

~~~~~~~~~~~~~{.py}
>>> b = Elf('/usr/bin/gdb')

>>> hex(b.getHeader().getEntry())
'0x45bc40L'
~~~~~~~~~~~~~

\section ElfHeader_py_api Python API - Methods of the ElfHeader class
<hr>

- <b>\ref py_ELF_page getEIClass(void)</b><br>
Returns the architecture size of this binary.<br>
e.g: `ELFCLASS64`

- <b>\ref py_ELF_page getEIData(void)</b><br>
Returns the endianness of the binary.<br>
e.g: `ELFDATA2LSB`

- <b>integer getEhsize(void)</b><br>
Returns the ELF header size. This member holds the ELF header's size in bytes.

- <b>integer getEntry(void)</b><br>
Returns the entry point. This member gives the virtual address to which the system
first transfers control, thus starting the process. If the file has no associated
entry point, this member holds zero.

- <b>\ref py_ELF_page getFlags(void)</b><br>
Returns the flags. This member holds processor-specific flags associated with the file.

- <b>\ref py_ELF_page getMachine(void)</b><br>
Returns the machine. This member specifies the required architecture for an individual file.

- <b>integer getPhentsize(void)</b><br>
Returns the program header entry size. This member holds the size in bytes of one entry
in the file's program header table - all entries are the same size.

- <b>integer getPhnum(void)</b><br>
Returns the number of program header entry. This member holds the number of entries in
the program header table. Thus the product of triton::format::elf::ElfHeader::phentsize
and triton::format::elf::ElfHeader::phnum gives the table's size in bytes.

- <b>integer getPhoff(void)</b><br>
Returns the program header offset. This member holds the program header table's file offset in
bytes. If the file has no program header table, this member holds zero.

- <b>integer getShentsize(void)</b><br>
Returns the section header entry size. This member holds a sections header's size in bytes. A
section header is one entry in the section header table - all entries are the same size.

- <b>integer getShnum(void)</b><br>
Returns the number of section header entry. This member holds the number of entries in the section
header table. Thus the product of triton::format::elf::ElfHeader::shentsize and triton::format::elf::ElfHeader::shnum
gives the section header table's size in bytes.

- <b>integer getShoff(void)</b><br>
Returns the section header offset. This member holds the section header table's file offset in bytes.
If the file has no section header table, this member holds zero.

- <b>integer getShstrndx(void)</b><br>
Returns the index of the string table. This member holds the section header table index of the entry
associated with the section name string table. If the file has no section name string table, this
member holds the value triton::format::elf::SHN_UNDEF.

- <b>\ref py_ELF_page getType(void)</b><br>
Returns the type. This member identifies the object file type.

- <b>\ref py_ELF_page getVersion(void)</b><br>
Returns the version. This member identifies the file version.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! ElfHeader destructor.
      void ElfHeader_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElfHeader_AsElfHeader(self);
        Py_DECREF(self);
      }


      static PyObject* ElfHeader_getEIClass(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getEIClass());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getEIData(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getEIData());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getEhsize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getEhsize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getEntry(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfHeader_AsElfHeader(self)->getEntry());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getFlags(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getFlags());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getMachine(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getMachine());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getPhentsize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getPhentsize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getPhnum(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getPhnum());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getPhoff(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfHeader_AsElfHeader(self)->getPhoff());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getShentsize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getShentsize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getShnum(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getShnum());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getShoff(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfHeader_AsElfHeader(self)->getShoff());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getShstrndx(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getShstrndx());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfHeader_getVersion(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfHeader_AsElfHeader(self)->getVersion());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfHeader methods.
      PyMethodDef ElfHeader_callbacks[] = {
        {"getEIClass",    ElfHeader_getEIClass,       METH_NOARGS,    ""},
        {"getEIData",     ElfHeader_getEIData,        METH_NOARGS,    ""},
        {"getEhsize",     ElfHeader_getEhsize,        METH_NOARGS,    ""},
        {"getEntry",      ElfHeader_getEntry,         METH_NOARGS,    ""},
        {"getFlags",      ElfHeader_getFlags,         METH_NOARGS,    ""},
        {"getMachine",    ElfHeader_getMachine,       METH_NOARGS,    ""},
        {"getPhentsize",  ElfHeader_getPhentsize,     METH_NOARGS,    ""},
        {"getPhnum",      ElfHeader_getPhnum,         METH_NOARGS,    ""},
        {"getPhoff",      ElfHeader_getPhoff,         METH_NOARGS,    ""},
        {"getShentsize",  ElfHeader_getShentsize,     METH_NOARGS,    ""},
        {"getShnum",      ElfHeader_getShnum,         METH_NOARGS,    ""},
        {"getShoff",      ElfHeader_getShoff,         METH_NOARGS,    ""},
        {"getShstrndx",   ElfHeader_getShstrndx,      METH_NOARGS,    ""},
        {"getType",       ElfHeader_getType,          METH_NOARGS,    ""},
        {"getVersion",    ElfHeader_getVersion,       METH_NOARGS,    ""},
        {nullptr,         nullptr,                    0,              nullptr}
      };


      PyTypeObject ElfHeader_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "ElfHeader",                                /* tp_name */
        sizeof(ElfHeader_Object),                   /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)ElfHeader_dealloc,              /* tp_dealloc */
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
        "ElfHeader objects",                        /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        ElfHeader_callbacks,                        /* tp_methods */
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


      PyObject* PyElfHeader(const triton::format::elf::ElfHeader& header) {
        ElfHeader_Object* object;

        PyType_Ready(&ElfHeader_Type);
        object = PyObject_NEW(ElfHeader_Object, &ElfHeader_Type);
        if (object != NULL)
          object->header = new triton::format::elf::ElfHeader(header);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
