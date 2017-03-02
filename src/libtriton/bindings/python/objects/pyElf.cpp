//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elf.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_Elf_page Elf
    \brief [**python api**] All information about the Elf python object.

\tableofcontents

\section py_Elf_description Description
<hr>

This object is used to represent the ELF binary format.

\subsection py_Elf_example Example

~~~~~~~~~~~~~{.py}
>>> b = Elf('/usr/bin/gdb')

>>> for lib in b.getSharedLibraries():
...     print lib
...
libreadline.so.6
libz.so.1
libdl.so.2
libncurses.so.5
libm.so.6
libpthread.so.0
libpython2.7.so.1.0
libc.so.6

>>> hex(b.getHeader().getEntry())
'0x45bc40L'

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

\subsection py_Elf_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> binary = Elf('/usr/bin/gdb')
~~~~~~~~~~~~~

\section Elf_py_api Python API - Methods of the Elf class
<hr>

- <b>[\ref py_ElfDynamicTable_page, ...] getDynamicTable(void)</b><br>
Returns the list of dynamic table entries.

- <b>\ref py_ElfHeader_page getHeader(void)</b><br>
Returns the ELF header.

- <b>string getPath(void)</b><br>
Returns the path of the parsed binary.<br>
e.g: `/usr/bin/gdb`

- <b>[\ref py_ElfProgramHeader_page, ...] getProgramHeaders(void)</b><br>
Returns the list of program headers.

- <b>bytes getRaw(void)</b><br>
Returns the raw binary.

- <b>[\ref py_ElfRelocationTable_page, ...] getRelocationTable(void)</b><br>
Returns the list of relocations table entries.

- <b>[\ref py_ElfSectionHeader_page, ...] getSectionHeaders(void)</b><br>
Returns the list of section headers.

- <b>[string, ...] getSharedLibraries(void)</b><br>
Returns the list of shared library dependencies.<br>
e.g: `["libc.so.6", "libncurses.so.5"]`

- <b>integer getSize(void)</b><br>
Returns the binary size.

- <b>[\ref py_ElfSymbolTable_page, ...] getSymbolsTable(void)</b><br>
Returns the list of symbols table entries.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! Elf destructor.
      void Elf_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElf_AsElf(self);
        Py_DECREF(self);
      }


      static PyObject* Elf_getDynamicTable(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::elf::ElfDynamicTable>& dyn = PyElf_AsElf(self)->getDynamicTable();
          ret = xPyList_New(dyn.size());
          for (triton::uint32 i = 0; i < dyn.size(); i++) {
            PyList_SetItem(ret, i, PyElfDynamicTable(dyn[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* Elf_getHeader(PyObject* self, PyObject* noarg) {
        try {
          return PyElfHeader(PyElf_AsElf(self)->getHeader());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Elf_getPath(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString(PyElf_AsElf(self)->getPath().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Elf_getProgramHeaders(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::elf::ElfProgramHeader>& phdr = PyElf_AsElf(self)->getProgramHeaders();
          ret = xPyList_New(phdr.size());
          for (triton::uint32 i = 0; i < phdr.size(); i++) {
            PyList_SetItem(ret, i, PyElfProgramHeader(phdr[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* Elf_getRaw(PyObject* self, PyObject* noarg) {
        try {
          const triton::uint8* raw = PyElf_AsElf(self)->getRaw();
          triton::usize size       = PyElf_AsElf(self)->getSize();
          return PyBytes_FromStringAndSize(reinterpret_cast<const char*>(raw), size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Elf_getRelocationTable(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::elf::ElfRelocationTable>& rel = PyElf_AsElf(self)->getRelocationTable();
          ret = xPyList_New(rel.size());
          for (triton::uint32 i = 0; i < rel.size(); i++) {
            PyList_SetItem(ret, i, PyElfRelocationTable(rel[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* Elf_getSectionHeaders(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::elf::ElfSectionHeader>& shdr = PyElf_AsElf(self)->getSectionHeaders();
          ret = xPyList_New(shdr.size());
          for (triton::uint32 i = 0; i < shdr.size(); i++) {
            PyList_SetItem(ret, i, PyElfSectionHeader(shdr[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* Elf_getSharedLibraries(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<std::string>& lib = PyElf_AsElf(self)->getSharedLibraries();
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


      static PyObject* Elf_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUsize(PyElf_AsElf(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* Elf_getSymbolsTable(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const std::vector<triton::format::elf::ElfSymbolTable>& sym = PyElf_AsElf(self)->getSymbolsTable();
          ret = xPyList_New(sym.size());
          for (triton::uint32 i = 0; i < sym.size(); i++) {
            PyList_SetItem(ret, i, PyElfSymbolTable(sym[i]));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      //! Elf methods.
      PyMethodDef Elf_callbacks[] = {
        {"getDynamicTable",       Elf_getDynamicTable,      METH_NOARGS,     ""},
        {"getHeader",             Elf_getHeader,            METH_NOARGS,     ""},
        {"getPath",               Elf_getPath,              METH_NOARGS,     ""},
        {"getProgramHeaders",     Elf_getProgramHeaders,    METH_NOARGS,     ""},
        {"getRaw",                Elf_getRaw,               METH_NOARGS,     ""},
        {"getRelocationTable",    Elf_getRelocationTable,   METH_NOARGS,     ""},
        {"getSectionHeaders",     Elf_getSectionHeaders,    METH_NOARGS,     ""},
        {"getSharedLibraries",    Elf_getSharedLibraries,   METH_NOARGS,     ""},
        {"getSize",               Elf_getSize,              METH_NOARGS,     ""},
        {"getSymbolsTable",       Elf_getSymbolsTable,      METH_NOARGS,     ""},
        {nullptr,                 nullptr,                  0,               nullptr}
      };


      PyTypeObject Elf_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "Elf",                                      /* tp_name */
        sizeof(Elf_Object),                         /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)Elf_dealloc,                    /* tp_dealloc */
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
        "Elf objects",                              /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        Elf_callbacks,                              /* tp_methods */
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


      PyObject* PyElf(const std::string& path) {
        Elf_Object* object;

        PyType_Ready(&Elf_Type);
        object = PyObject_NEW(Elf_Object, &Elf_Type);
        if (object != NULL)
          object->elf = new triton::format::elf::Elf(path);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
