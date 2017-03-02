//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfProgramHeader.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_ElfProgramHeader_page ElfProgramHeader
    \brief [**python api**] All information about the ElfProgramHeader python object.

\tableofcontents

\section py_ElfProgramHeader_description Description
<hr>

This object is used to represent a Program Header entry from the ELF binary format.

\subsection py_ElfProgramHeader_example Example

~~~~~~~~~~~~~{.py}
>>> binary = Elf('/usr/bin/gdb')

>>> phdr = binary.getProgramHeaders()
>>> for p in phdr:
...     if p.getType() == ELF.PT_LOAD:
...             print hex(p.getVaddr())
...
0x400000L
0xbfdda0L
~~~~~~~~~~~~~

\section ElfProgramHeader_py_api Python API - Methods of the ElfProgramHeader class
<hr>

- <b>integer getAlign(void)</b><br>
Returns the segment alignment. This member holds the value to which the segments are
aligned in memory and in the file.

- <b>integer getFilesz(void)</b><br>
Returns the file image size. This member holds the number of bytes in the file image
of the segment. It may be zero.

- <b>\ref py_ELF_page getFlags(void)</b><br>
Returns the flags. This member holds a bit mask of flags relevant to the segment.<br>
e.g: `PF_X`

- <b>integer getMemsz(void)</b><br>
Returns the memory image size. This member holds the number of bytes in the memory
image of the segment. It may be zero.

- <b>integer getOffset(void)</b><br>
Returns the offset. This member holds the offset from the beginning of the file at
which the first byte of the segment resides.

- <b>integer getPaddr(void)</b><br>
Returns the physical address. On systems for which physical addressing is relevant,
this member is reserved for the segment's physical address. Under BSD this member is
not used and must be zero.

- <b>\ref py_ELF_page getType(void)</b><br>
Returns the type. This member indicates what kind of segment this array element describes
or how to interpret the array element's information.

- <b>integer getVaddr(void)</b><br>
Returns the virtual address. This member holds the virtual address at which the first byte
of the segment resides in memory.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! ElfProgramHeader destructor.
      void ElfProgramHeader_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElfProgramHeader_AsElfProgramHeader(self);
        Py_DECREF(self);
      }


      static PyObject* ElfProgramHeader_getAlign(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfProgramHeader_AsElfProgramHeader(self)->getAlign());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getFilesz(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfProgramHeader_AsElfProgramHeader(self)->getFilesz());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getFlags(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfProgramHeader_AsElfProgramHeader(self)->getFlags());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getMemsz(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfProgramHeader_AsElfProgramHeader(self)->getMemsz());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getOffset(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfProgramHeader_AsElfProgramHeader(self)->getOffset());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getPaddr(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfProgramHeader_AsElfProgramHeader(self)->getPaddr());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfProgramHeader_AsElfProgramHeader(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfProgramHeader_getVaddr(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfProgramHeader_AsElfProgramHeader(self)->getVaddr());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfProgramHeader methods.
      PyMethodDef ElfProgramHeader_callbacks[] = {
        {"getAlign",      ElfProgramHeader_getAlign,    METH_NOARGS,    ""},
        {"getFilesz",     ElfProgramHeader_getFilesz,   METH_NOARGS,    ""},
        {"getFlags",      ElfProgramHeader_getFlags,    METH_NOARGS,    ""},
        {"getMemsz",      ElfProgramHeader_getMemsz,    METH_NOARGS,    ""},
        {"getOffset",     ElfProgramHeader_getOffset,   METH_NOARGS,    ""},
        {"getPaddr",      ElfProgramHeader_getPaddr,    METH_NOARGS,    ""},
        {"getType",       ElfProgramHeader_getType,     METH_NOARGS,    ""},
        {"getVaddr",      ElfProgramHeader_getVaddr,    METH_NOARGS,    ""},
        {nullptr,         nullptr,                      0,              nullptr}
      };


      PyTypeObject ElfProgramHeader_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "ElfProgramHeader",                         /* tp_name */
        sizeof(ElfProgramHeader_Object),            /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)ElfProgramHeader_dealloc,       /* tp_dealloc */
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
        "ElfProgramHeader objects",                 /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        ElfProgramHeader_callbacks,                 /* tp_methods */
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


      PyObject* PyElfProgramHeader(const triton::format::elf::ElfProgramHeader& phdr) {
        ElfProgramHeader_Object* object;

        PyType_Ready(&ElfProgramHeader_Type);
        object = PyObject_NEW(ElfProgramHeader_Object, &ElfProgramHeader_Type);
        if (object != NULL)
          object->phdr = new triton::format::elf::ElfProgramHeader(phdr);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
