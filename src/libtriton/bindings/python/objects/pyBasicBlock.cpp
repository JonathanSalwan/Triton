//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/coreUtils.hpp>
#include <triton/exceptions.hpp>
#include <triton/basicBlock.hpp>

#include <iostream>


/* setup doctest context

>>> from __future__ import print_function
>>> from triton import *
>>> ctx = TritonContext(ARCH.X86_64)

*/

/*! \page py_BasicBlock_page BasicBlock
    \brief [**python api**] All information about the BasicBlock Python object.

\tableofcontents

\section py_BasicBlock_description Description
<hr>

This object is used to represent a basic block of instructions.

\subsection py_BasicBlock_example Example

~~~~~~~~~~~~~{.py}
>>> block = BasicBlock([
...     Instruction(b"\xc9"),
...     Instruction(b"\xc3")
... ])

>>> print(block)
0x0: <not disassembled>
0x1: <not disassembled>

>>> # Disassemble a block
>>> ctx.disassembly(block)
>>> print(block)
0x0: leave
0x1: ret

>>> # Disassemble a block with a given base address
>>> ctx.disassembly(block, 0x400000)
>>> print(block)
0x400000: leave
0x400001: ret

>>> hex(block.getFirstAddress())
'0x400000'

>>> hex(block.getLastAddress())
'0x400001'

# Remove an instruction in the block
>>> block.remove(1)
True
>>> print(block)
0x400000: leave

# Add instructions in the block
>>> block.add(Instruction(b"\x90"))
>>> block.add(Instruction(b"\xc3"))
>>> ctx.disassembly(block, 0x400000)
>>> print(block)
0x400000: leave
0x400001: nop
0x400002: ret

# Process a block
>>> ctx.processing(block)
0

~~~~~~~~~~~~~

\subsection py_BasicBlock_constructor Constructor

~~~~~~~~~~~~~{.py}
# Constructor by default
>>> block = BasicBlock()
>>> block.add(Instruction(b"\xc9"))
>>> block.add(Instruction(b"\xc3"))
>>>

# Constructor with a list of instructions
>>> block = BasicBlock([
...     Instruction(b"\xc9"),
...     Instruction(b"\xc3")
... ])
>>>

~~~~~~~~~~~~~

\section BasicBlock_py_api Python API - Methods of the BasicBlock class
<hr>

- <b>void add(\ref py_Instruction_page inst)</b><br>
Adds an instruction to the block.

- <b>integer getFirstAddress(void)</b><br>
Returns the first instruction's address of the block.

- <b>[\ref py_Instruction_page, ...] getInstructions(void)</b><br>
Returns all instructions of the block.

- <b>integer getLastAddress(void)</b><br>
Returns the last instruction's address of the block.

- <b>integer getSize(void)</b><br>
Returns the number of instruction in the block.

- <b>bool remove(integer position)</b><br>
Removes the instruction in the block at a given position. Returns true if successed.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! BasicBlock destructor.
      void BasicBlock_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyBasicBlock_AsBasicBlock(self);
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static PyObject* BasicBlock_add(PyObject* self, PyObject* instruction) {
        try {
          if (!PyInstruction_Check(instruction))
            return PyErr_Format(PyExc_TypeError, "BasicBlock::add(): Expected an Instruction as argument.");
          PyBasicBlock_AsBasicBlock(self)->add(*PyInstruction_AsInstruction(instruction));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BasicBlock_getFirstAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyBasicBlock_AsBasicBlock(self)->getFirstAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BasicBlock_getInstructions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize index = 0;

        try {
          auto insts = PyBasicBlock_AsBasicBlock(self)->getInstructions();
          ret = xPyList_New(insts.size());
          for (auto& inst : insts)
            PyList_SetItem(ret, index++, PyInstruction(inst));
          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BasicBlock_getLastAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyBasicBlock_AsBasicBlock(self)->getLastAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BasicBlock_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyBasicBlock_AsBasicBlock(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* BasicBlock_remove(PyObject* self, PyObject* position) {
        try {
          if (!PyLong_Check(position) && !PyInt_Check(position))
            return PyErr_Format(PyExc_TypeError, "BasicBlock::remove(): Expected an integer as argument.");
          if (PyBasicBlock_AsBasicBlock(self)->remove(PyLong_AsUint64(position)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      #if !defined(IS_PY3_8) || !IS_PY3_8
      static int BasicBlock_print(PyObject* self, void* io, int s) {
        std::cout << PyBasicBlock_AsBasicBlock(self);
        return 0;
      }
      #endif


      static PyObject* BasicBlock_str(PyObject* self) {
        try {
          return PyStr_FromFormat("%s", triton::utils::toString(PyBasicBlock_AsBasicBlock(self)).c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! BasicBlock methods.
      PyMethodDef BasicBlock_callbacks[] = {
        {"add",               BasicBlock_add,               METH_O,         ""},
        {"getFirstAddress",   BasicBlock_getFirstAddress,   METH_NOARGS,    ""},
        {"getInstructions",   BasicBlock_getInstructions,   METH_NOARGS,    ""},
        {"getLastAddress",    BasicBlock_getLastAddress,    METH_NOARGS,    ""},
        {"getSize",           BasicBlock_getSize,           METH_NOARGS,    ""},
        {"remove",            BasicBlock_remove,            METH_O,         ""},
        {nullptr,             nullptr,                      0,              nullptr}
      };


      PyTypeObject BasicBlock_Type = {
        PyVarObject_HEAD_INIT(&PyType_Type, 0)
        "BasicBlock",                               /* tp_name */
        sizeof(BasicBlock_Object),                  /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)BasicBlock_dealloc,             /* tp_dealloc */
        #if IS_PY3_8
        0,                                          /* tp_vectorcall_offset */
        #else
        (printfunc)BasicBlock_print,                /* tp_print */
        #endif
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        (reprfunc)BasicBlock_str,                   /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)BasicBlock_str,                   /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "BasicBlock objects",                       /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        BasicBlock_callbacks,                       /* tp_methods */
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
        #if IS_PY3
          0,                                        /* tp_version_tag */
          0,                                        /* tp_finalize */
          #if IS_PY3_8
            0,                                      /* tp_vectorcall */
            #if !IS_PY3_9
              0,                                    /* bpo-37250: kept for backwards compatibility in CPython 3.8 only */
            #endif
          #endif
        #else
          0                                         /* tp_version_tag */
        #endif
      };


      PyObject* PyBasicBlock(const triton::arch::BasicBlock& block) {
        BasicBlock_Object* object;

        PyType_Ready(&BasicBlock_Type);
        object = PyObject_NEW(BasicBlock_Object, &BasicBlock_Type);
        if (object != NULL)
          object->block = new triton::arch::BasicBlock(block);

        return (PyObject*)object;
      }


      PyObject* PyBasicBlock(std::vector<triton::arch::Instruction>& insts) {
        BasicBlock_Object* object;

        PyType_Ready(&BasicBlock_Type);
        object = PyObject_NEW(BasicBlock_Object, &BasicBlock_Type);
        if (object != NULL)
          object->block = new triton::arch::BasicBlock(insts);

        return (PyObject*)object;
      }


      PyObject* PyBasicBlock(void) {
        BasicBlock_Object* object;

        PyType_Ready(&BasicBlock_Type);
        object = PyObject_NEW(BasicBlock_Object, &BasicBlock_Type);
        if (object != NULL)
          object->block = new triton::arch::BasicBlock();

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
