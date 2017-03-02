//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>



/*! \page py_MemoryAccess_page MemoryAccess
    \brief [**python api**] All information about the memory access python object.

\tableofcontents

\section py_Memory_description Description
<hr>

This object is used to represent a memory access.

\subsection py_MemoryAccess_example Example

~~~~~~~~~~~~~{.py}
>>> processing(inst)
>>> print inst
40000: mov ah, byte ptr [rdx + rcx*2 + 0x100]

>>> op1 = inst.getOperands()[1]
>>> print op1
[@0x6135a]:8 bv[7..0]

>>> print op1.getBaseRegister()
rdx:64 bv[63..0]

>>> print op1.getIndexRegister()
rcx:64 bv[63..0]

>>> print op1.getScale()
0x2:8 bv[7..0]

>>> print op1.getDisplacement()
0x100:8 bv[7..0]

>>> print op1.getLeaAst()
(bvadd (_ bv397882 64) (bvadd (bvmul (_ bv16 64) (_ bv2 64)) (_ bv256 64)))

>>> print hex(op1.getLeaAst().evaluate())
0x6135aL

>>> print hex(op1.getAddress())
0x6135aL

>>> print op1.getSize()
1
~~~~~~~~~~~~~

\subsection py_MemoryAccess_constructor Constructor

~~~~~~~~~~~~~{.py}
>>> mem = MemoryAccess(0x400f4d3, 8, 0x6162636465666768)
>>> print mem
[@0x400f4d3]:64 bv[63..0]

>>> hex(mem.getAddress())
'0x400f4d3'

>>> mem.getSize()
8

>>> hex(mem.getConcreteValue())
'0x6162636465666768L'
~~~~~~~~~~~~~

\section MemoryAccess_py_api Python API - Methods of the MemoryAccess class
<hr>

- <b>integer getAddress(void)</b><br>
Returns the target address of the memory access.<br>
e.g: `0x7fffdd745ae0`

- <b>\ref py_Register_page getBaseRegister(void)</b><br>
Returns the base register (if exists) of the memory access<br>

- <b>integer getBitSize(void)</b><br>
Returns the size (in bits) of the memory access.<br>
e.g: `64`

- <b>\ref py_Bitvector_page getBitvector(void)</b><br>
Returns the bitvector of the memory cells.

- <b>integer getConcreteValue(void)</b><br>
Returns the concrete value. It's basically the content which has been LOADED or STORED. Note that getting the
concrete value does not relfect the real internal memory state. If you want to know the internal state of a memory cell, use
the triton::API::getConcreteMemoryValue() function.

- <b>\ref py_Immediate_page getDisplacement(void)</b><br>
Returns the displacement (if exists) of the memory access.

- <b>\ref py_Register_page getIndexRegister(void)</b><br>
Returns the index register (if exists) of the memory access.<br>

- <b>\ref py_AstNode_page getLeaAst(void)</b><br>
Returns the AST of the memory access (LEA).

- <b>\ref py_Immediate_page getScale(void)</b><br>
Returns the scale (if exists) of the  memory access.

- <b>\ref py_Register_page getSegmentRegister(void)</b><br>
Returns the segment register (if exists) of the memory access. Note that to be user-friendly, the
segment register is used as base register and not as a selector into the GDT.<br>

- <b>integer getSize(void)</b><br>
Returns the size (in bytes) of the  memory access.<br>
e.g: `8`

- <b>\ref py_OPERAND_page getType(void)</b><br>
Returns type of the memory access. In this case this function returns `OPERAND.MEM`.

- <b>bool isOverlapWith(\ref py_MemoryAccess_page other)</b><br>
Returns true if `other` and `self` overlap.

- <b>void setBaseRegister(\ref py_Register_page reg)</b><br>
Sets the base register of the memory access.

- <b>void setConcreteValue(integer value)</b><br>
Sets a concrete value to this memory access. Note that by setting the concrete value does not affect the internal memory value.
If you want to define a concrete value at a specific memory cells, use the triton::API::setConcreteMemoryValue() function.

- <b>void setDisplacement(\ref py_Immediate_page imm)</b><br>
Sets the displacement of the memory access.

- <b>void setIndexRegister(\ref py_Register_page reg)</b><br>
Sets the index register of the memory' access.

- <b>void setScale(\ref py_Immediate_page imm)</b><br>
Sets the scale of the memory access.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! MemoryAccess destructor.
      void MemoryAccess_dealloc(PyObject* self) {
        std::cout << std::flush;
        delete PyMemoryAccess_AsMemoryAccess(self);
        Py_DECREF(self);
      }


      static PyObject* MemoryAccess_getAddress(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint64(PyMemoryAccess_AsMemoryAccess(self)->getAddress());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getLeaAst(PyObject* self, PyObject* noarg) {
        try {
          if (PyMemoryAccess_AsMemoryAccess(self)->getLeaAst() == nullptr) {
            Py_INCREF(Py_None);
            return Py_None;
          }
          return PyAstNode(PyMemoryAccess_AsMemoryAccess(self)->getLeaAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getBaseRegister(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Register reg(PyMemoryAccess_AsMemoryAccess(self)->getBaseRegister());
          return PyRegister(reg);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getBitSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyMemoryAccess_AsMemoryAccess(self)->getBitSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getBitvector(PyObject* self, PyObject* noarg) {
        try {
          return PyBitvector(*PyMemoryAccess_AsMemoryAccess(self));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getConcreteValue(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyMemoryAccess_AsMemoryAccess(self)->getConcreteValue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getDisplacement(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Immediate imm(PyMemoryAccess_AsMemoryAccess(self)->getDisplacement());
          return PyImmediate(imm);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getIndexRegister(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Register reg(PyMemoryAccess_AsMemoryAccess(self)->getIndexRegister());
          return PyRegister(reg);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getScale(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Immediate imm(PyMemoryAccess_AsMemoryAccess(self)->getScale());
          return PyImmediate(imm);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getSegmentRegister(PyObject* self, PyObject* noarg) {
        try {
          triton::arch::Register reg(PyMemoryAccess_AsMemoryAccess(self)->getSegmentRegister());
          return PyRegister(reg);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyMemoryAccess_AsMemoryAccess(self)->getSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyMemoryAccess_AsMemoryAccess(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_isOverlapWith(PyObject* self, PyObject* mem2) {
        try {
          triton::arch::MemoryAccess* mem1;

          if (!PyMemoryAccess_Check(mem2))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::isOverlapWith(): Expected a MemoryAccess as argument.");

          mem1 = PyMemoryAccess_AsMemoryAccess(self);
          if (mem1->isOverlapWith(*PyMemoryAccess_AsMemoryAccess(mem2)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_setBaseRegister(PyObject* self, PyObject* reg) {
        try {
          triton::arch::MemoryAccess* mem;

          if (!PyRegister_Check(reg))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::setBaseRegister(): Expected a Register as argument.");

          mem = PyMemoryAccess_AsMemoryAccess(self);
          mem->setBaseRegister(*PyRegister_AsRegister(reg));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_setConcreteValue(PyObject* self, PyObject* value) {
        try {
          triton::arch::MemoryAccess* mem;

          if (!PyLong_Check(value) && !PyInt_Check(value))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::setConcretevalue(): Expected an integer as argument.");

          mem = PyMemoryAccess_AsMemoryAccess(self);
          mem->setConcreteValue(PyLong_AsUint512(value));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_setDisplacement(PyObject* self, PyObject* imm) {
        try {
          triton::arch::MemoryAccess* mem;

          if (!PyImmediate_Check(imm))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::setDisplacement(): Expected an Immediate as argument.");

          mem = PyMemoryAccess_AsMemoryAccess(self);
          mem->setDisplacement(*PyImmediate_AsImmediate(imm));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_setIndexRegister(PyObject* self, PyObject* reg) {
        try {
          triton::arch::MemoryAccess* mem;

          if (!PyRegister_Check(reg))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::setIndexRegister(): Expected a Register as argument.");

          mem = PyMemoryAccess_AsMemoryAccess(self);
          mem->setIndexRegister(*PyRegister_AsRegister(reg));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_setScale(PyObject* self, PyObject* imm) {
        try {
          triton::arch::MemoryAccess* mem;

          if (!PyImmediate_Check(imm))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::setScale(): Expected an Immediate as argument.");

          mem = PyMemoryAccess_AsMemoryAccess(self);
          mem->setScale(*PyImmediate_AsImmediate(imm));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* MemoryAccess_setSegmentRegister(PyObject* self, PyObject* reg) {
        try {
          triton::arch::MemoryAccess* mem;

          if (!PyRegister_Check(reg))
            return PyErr_Format(PyExc_TypeError, "MemoryAccess::setSegmentRegister(): Expected a Register as argument.");

          mem = PyMemoryAccess_AsMemoryAccess(self);
          mem->setSegmentRegister(*PyRegister_AsRegister(reg));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int MemoryAccess_print(PyObject* self) {
        std::cout << PyMemoryAccess_AsMemoryAccess(self);
        return 0;
      }


      static PyObject* MemoryAccess_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyMemoryAccess_AsMemoryAccess(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! MemoryAccess methods.
      PyMethodDef MemoryAccess_callbacks[] = {
        {"getAddress",          MemoryAccess_getAddress,         METH_NOARGS,      ""},
        {"getBaseRegister",     MemoryAccess_getBaseRegister,    METH_NOARGS,      ""},
        {"getBitSize",          MemoryAccess_getBitSize,         METH_NOARGS,      ""},
        {"getBitvector",        MemoryAccess_getBitvector,       METH_NOARGS,      ""},
        {"getConcreteValue",    MemoryAccess_getConcreteValue,   METH_NOARGS,      ""},
        {"getDisplacement",     MemoryAccess_getDisplacement,    METH_NOARGS,      ""},
        {"getIndexRegister",    MemoryAccess_getIndexRegister,   METH_NOARGS,      ""},
        {"getLeaAst",           MemoryAccess_getLeaAst,          METH_NOARGS,      ""},
        {"getScale",            MemoryAccess_getScale,           METH_NOARGS,      ""},
        {"getSegmentRegister",  MemoryAccess_getSegmentRegister, METH_NOARGS,      ""},
        {"getSize",             MemoryAccess_getSize,            METH_NOARGS,      ""},
        {"getType",             MemoryAccess_getType,            METH_NOARGS,      ""},
        {"isOverlapWith",       MemoryAccess_isOverlapWith,      METH_O,           ""},
        {"setBaseRegister",     MemoryAccess_setBaseRegister,    METH_O,           ""},
        {"setConcreteValue",    MemoryAccess_setConcreteValue,   METH_O,           ""},
        {"setDisplacement",     MemoryAccess_setDisplacement,    METH_O,           ""},
        {"setIndexRegister",    MemoryAccess_setIndexRegister,   METH_O,           ""},
        {"setScale",            MemoryAccess_setScale,           METH_O,           ""},
        {"setSegmentRegister",  MemoryAccess_setSegmentRegister, METH_O,           ""},
        {nullptr,               nullptr,                         0,                nullptr}
      };


      PyTypeObject MemoryAccess_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "MemoryAccess",                             /* tp_name */
        sizeof(MemoryAccess_Object),                /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)MemoryAccess_dealloc,           /* tp_dealloc */
        (printfunc)MemoryAccess_print,              /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)MemoryAccess_str,                 /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "MemoryAccess objects",                     /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        MemoryAccess_callbacks,                     /* tp_methods */
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


      PyObject* PyMemoryAccess(const triton::arch::MemoryAccess& mem) {
        MemoryAccess_Object* object;

        PyType_Ready(&MemoryAccess_Type);
        object = PyObject_NEW(MemoryAccess_Object, &MemoryAccess_Type);
        if (object != NULL)
          object->mem = new triton::arch::MemoryAccess(mem);

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
