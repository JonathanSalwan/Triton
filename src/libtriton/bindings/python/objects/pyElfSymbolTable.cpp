//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfSymbolTable.hpp>
#include <triton/exceptions.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_ElfSymbolTable_page ElfSymbolTable
    \brief [**python api**] All information about the ElfSymbolTable python object.

\tableofcontents

\section py_ElfSymbolTable_description Description
<hr>

This object is used to represent a Section Header entry from the ELF binary format.

\subsection py_ElfSymbolTable_example Example

~~~~~~~~~~~~~{.py}
>>> binary = Elf('/usr/bin/gdb')

>>> syms = binary.getSymbolsTable()
>>> for sym in syms:
...     print sym.getName()
...
PyList_Insert
PyInt_GetMax
scrollok
PyModule_AddObject
def_shell_mode
ctime
chmod
tcsetattr
PySys_GetObject
PyDict_SetItemString
pipe2
chdir
fileno
dup2
[...]
~~~~~~~~~~~~~

\section ElfSymbolTable_py_api Python API - Methods of the ElfSymbolTable class
<hr>

- <b>integer getIdxname(void)</b><br>
Returns the section index name. This member holds an index into the object file's
symbol string table, which holds the character representations of the symbol names.
If the value is non-zero, it represents a string table index that gives the symbol
name. Otherwise, the symbol table entry has no name.

- <b>\ref py_ELF_page getInfo(void)</b><br>
Returns the section info. This member specifies the symbol's type and binding attributes.
A list of the values and meanings appears below.

- <b>string getName(void)</b><br>
Returns the section name. This member specifies the name of the symbol as string
based on the triton::format::elf::ElfSymbolTable::idxname.<br>
e.g: `main`

- <b>\ref py_ELF_page getOther(void)</b><br>
Returns the other field of the symbol table structure. This member currently specifies a
symbol's visibility.

- <b>integer getShndx(void)</b><br>
Returns the shndx field of the symbol table structure. Every symbol table entry is defined
in relation to some section. This member holds the relevant section header table index.
As the sh_link and sh_info interpretation table and the related text describe, some section
indexes indicate special meanings. If this member contains triton::format::elf::SHN_XINDEX,
then the actual section header index is too large to fit in this field. The actual value is
contained in the associated section of type triton::format::elf::SHT_SYMTAB_SHNDX.

- <b>integer getSize(void)</b><br>
Returns the section size. Many symbols have associated sizes. For example, a data object's size
is the number of bytes contained in the object. This member holds 0 if the symbol has no size or
an unknown size.

- <b>integer getValue(void)</b><br>
Returns the symbol value. This member gives the value of the associated symbol. Depending on
the context, this may be an absolute value, an address, and so on.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! ElfSymbolTable destructor.
      void ElfSymbolTable_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyElfSymbolTable_AsElfSymbolTable(self);
        Py_DECREF(self);
      }


      static PyObject* ElfSymbolTable_getIdxname(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSymbolTable_AsElfSymbolTable(self)->getIdxname());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSymbolTable_getInfo(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSymbolTable_AsElfSymbolTable(self)->getInfo());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSymbolTable_getName(PyObject* self, PyObject* noarg) {
        try {
          return PyString_FromString(PyElfSymbolTable_AsElfSymbolTable(self)->getName().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSymbolTable_getOther(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSymbolTable_AsElfSymbolTable(self)->getOther());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSymbolTable_getShndx(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyElfSymbolTable_AsElfSymbolTable(self)->getShndx());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSymbolTable_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSymbolTable_AsElfSymbolTable(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ElfSymbolTable_getValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyElfSymbolTable_AsElfSymbolTable(self)->getValue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! ElfSymbolTable methods.
      PyMethodDef ElfSymbolTable_callbacks[] = {
        {"getIdxname",    ElfSymbolTable_getIdxname,    METH_NOARGS,    ""},
        {"getInfo",       ElfSymbolTable_getInfo,       METH_NOARGS,    ""},
        {"getName",       ElfSymbolTable_getName,       METH_NOARGS,    ""},
        {"getOther",      ElfSymbolTable_getOther,      METH_NOARGS,    ""},
        {"getShndx",      ElfSymbolTable_getShndx,      METH_NOARGS,    ""},
        {"getSize",       ElfSymbolTable_getSize,       METH_NOARGS,    ""},
        {"getValue",      ElfSymbolTable_getValue,      METH_NOARGS,    ""},
        {nullptr,         nullptr,                      0,              nullptr}
      };


      PyTypeObject ElfSymbolTable_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "ElfSymbolTable",                           /* tp_name */
        sizeof(ElfSymbolTable_Object),              /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)ElfSymbolTable_dealloc,         /* tp_dealloc */
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
        "ElfSymbolTable objects",                   /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        ElfSymbolTable_callbacks,                   /* tp_methods */
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


      PyObject* PyElfSymbolTable(const triton::format::elf::ElfSymbolTable& sym) {
        ElfSymbolTable_Object* object;

        PyType_Ready(&ElfSymbolTable_Type);
        object = PyObject_NEW(ElfSymbolTable_Object, &ElfSymbolTable_Type);
        if (object != NULL)
          object->sym = new triton::format::elf::ElfSymbolTable(sym);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
