//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfRelocationTable.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_ElfRelocationTable_page ElfRelocationTable
    \brief [**python api**] All information about the ElfRelocationTable python object.

\tableofcontents

\section py_ElfRelocationTable_description Description
<hr>

This object is used to represent a Relocation Table entry from the ELF binary format.

\subsection py_ElfRelocationTable_example Example

~~~~~~~~~~~~~{.py}
>>> binary = Elf('/usr/bin/gdb')

>>> symbols = binary.getSymbolsTable()
>>> relocations = binary.getRelocationTable()

>>> for rel in relocations:
...     print hex(rel.getOffset()), symbols[rel.getSymidx()].getName()
...
0xbfdff8L __gmon_start__
0xc12280L rl_completion_query_items
0xc122a0L _Py_ZeroStruct
0xc122b8L PyExc_StopIteration
0xc122c0L history_base
0xc12300L PyBool_Type
0xc12488L history_length
0xc12490L stdscr
0xc12498L _rl_complete_mark_directories
0xc124a0L rl_instream
0xc124a8L __environ
0xc124b0L PyExc_ValueError
0xc124b8L _PyOS_ReadlineTState
0xc124c0L curscr
[...]
~~~~~~~~~~~~~

\section ElfRelocationTable_py_api Python API - Methods of the ElfRelocationTable class
<hr>

- <b>\ref py_ELF_page getAddend(void)</b><br>
Returns the relocation addend. This member specifies a constant addend used to compute the
value to be stored into the relocatable field.

- <b>\ref py_ELF_page getInfo(void)</b><br>
Returns the relocation info. This member gives both the symbol table index with respect to
which the relocation must be made and the type of relocation to apply. Relocation types are
processor-specific.

- <b>integer getOffset(void)</b><br>
Returns the relocation offset. This member gives the location at which to apply the relocation action.
For a relocatable file, the value is the byte offset from the beginning of the section to the storage
unit affected by the relocation. For an executable file or shared object, the value is the virtual address
of the storage unit affected by the relocation.

- <b>integer getSymidx(void)</b><br>
Returns the relocation symbol index. According to the triton::format::elf::ElfRelocationTable::info value, this field contains
the index of the corresponding symbol.

- <b>\ref py_ELF_page getType(void)</b><br>
Returns the type. According to the triton::format::elf::ElfRelocationTable::info value, this field contains the type of the
relocation.

- <b>bool isAddend(void)</b><br>
Returns true if this class is a triton::format::elf::DT_RELA otherwise false if it's a triton::format::elf::DT_REL.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! ElfRelocationTable destructor.
      void ElfRelocationTable_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElfRelocationTable_AsElfRelocationTable(self);
        Py_DECREF(self);
      }


      static PyObject* ElfRelocationTable_getAddend(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfRelocationTable_AsElfRelocationTable(self)->getAddend());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfRelocationTable_getInfo(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfRelocationTable_AsElfRelocationTable(self)->getInfo());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfRelocationTable_getOffset(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfRelocationTable_AsElfRelocationTable(self)->getOffset());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfRelocationTable_getSymidx(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfRelocationTable_AsElfRelocationTable(self)->getSymidx());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfRelocationTable_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfRelocationTable_AsElfRelocationTable(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfRelocationTable_isAddend(PyObject* self, PyObject* noarg) {
        try {
          if (PyElfRelocationTable_AsElfRelocationTable(self)->isAddend())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfRelocationTable methods.
      PyMethodDef ElfRelocationTable_callbacks[] = {
        {"getAddend",     ElfRelocationTable_getAddend,   METH_NOARGS,    ""},
        {"getInfo",       ElfRelocationTable_getInfo,     METH_NOARGS,    ""},
        {"getOffset",     ElfRelocationTable_getOffset,   METH_NOARGS,    ""},
        {"getSymidx",     ElfRelocationTable_getSymidx,   METH_NOARGS,    ""},
        {"getType",       ElfRelocationTable_getType,     METH_NOARGS,    ""},
        {"isAddend",      ElfRelocationTable_isAddend,    METH_NOARGS,    ""},
        {nullptr,         nullptr,                        0,              nullptr}
      };


      PyTypeObject ElfRelocationTable_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "ElfRelocationTable",                       /* tp_name */
        sizeof(ElfRelocationTable_Object),          /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)ElfRelocationTable_dealloc,     /* tp_dealloc */
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
        "ElfRelocationTable objects",               /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        ElfRelocationTable_callbacks,               /* tp_methods */
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


      PyObject* PyElfRelocationTable(const triton::format::elf::ElfRelocationTable& rel) {
        ElfRelocationTable_Object* object;

        PyType_Ready(&ElfRelocationTable_Type);
        object = PyObject_NEW(ElfRelocationTable_Object, &ElfRelocationTable_Type);
        if (object != NULL)
          object->rel = new triton::format::elf::ElfRelocationTable(rel);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
