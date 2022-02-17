//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/exceptions.hpp>
#include <triton/symbolicExpression.hpp>



/*! \page py_SymbolicExpression_page SymbolicExpression
    \brief [**python api**] All information about the SymbolicExpression Python object.

\tableofcontents

\section py_SymbolicExpression_description Description
<hr>

This object is used to represent a symbolic expression.

~~~~~~~~~~~~~{.py}
>>> from __future__ import print_function
>>> from triton import TritonContext, ARCH, Instruction, REG

>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> opcode = b"\x48\x31\xD0"
>>> inst = Instruction()

>>> inst.setOpcode(opcode)
>>> inst.setAddress(0x400000)
>>> ctxt.setConcreteRegisterValue(ctxt.registers.rax, 12345)
>>> ctxt.setConcreteRegisterValue(ctxt.registers.rdx, 67890)

>>> ctxt.processing(inst)
True
>>> print(inst)
0x400000: xor rax, rdx

>>> for expr in inst.getSymbolicExpressions():
...     print(expr)
...
(define-fun ref!0 () (_ BitVec 64) (bvxor (_ bv12345 64) (_ bv67890 64))) ; XOR operation
(define-fun ref!1 () (_ BitVec 1) (_ bv0 1)) ; Clears carry flag
(define-fun ref!2 () (_ BitVec 1) (_ bv0 1)) ; Clears overflow flag
(define-fun ref!3 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv0 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv1 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv2 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv3 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv4 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv5 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv6 8)))) ((_ extract 0 0) (bvlshr ((_ extract 7 0) ref!0) (_ bv7 8))))) ; Parity flag
(define-fun ref!4 () (_ BitVec 1) ((_ extract 63 63) ref!0)) ; Sign flag
(define-fun ref!5 () (_ BitVec 1) (ite (= ref!0 (_ bv0 64)) (_ bv1 1) (_ bv0 1))) ; Zero flag
(define-fun ref!6 () (_ BitVec 64) (_ bv4194307 64)) ; Program Counter

>>> expr_1 = inst.getSymbolicExpressions()[0]
>>> print(expr_1)
(define-fun ref!0 () (_ BitVec 64) (bvxor (_ bv12345 64) (_ bv67890 64))) ; XOR operation

>>> print(expr_1.getId())
0

>>> ast = expr_1.getAst()
>>> print(ast)
(bvxor (_ bv12345 64) (_ bv67890 64))


>>> expr_1.isMemory()
False

>>> expr_1.isRegister()
True

>>> print(expr_1.getOrigin())
rax:64 bv[63..0]

>>> print(expr_1.getDisassembly())
0x400000: xor rax, rdx

~~~~~~~~~~~~~

\section SymbolicExpression_py_api Python API - Methods of the SymbolicExpression class
<hr>

- <b>\ref py_AstNode_page getAst(void)</b><br>
Returns the AST root node of the symbolic expression.

- <b>string getComment(void)</b><br>
Returns the comment (if exists) of the symbolic expression.

- <b>string getDisassembly(void)</b><br>
Returns the instruction disassembly where the symbolic expression comes from.

- <b>integer getId(void)</b><br>
Returns the id of the symbolic expression. This id is always unique.<br>
e.g: `2387`

- <b>\ref py_AstNode_page getNewAst(void)</b><br>
Returns a new AST root node of the symbolic expression. This new instance is a duplicate of the original node and may be changed without changing the original semantics.

- <b>\ref py_MemoryAccess_page / \ref py_Register_page getOrigin(void)</b><br>
Returns the origin of the symbolic expression. For example, if the symbolic expression is assigned to a memory cell, this function returns
a \ref py_MemoryAccess_page, else if it is assigned to a register, this function returns a \ref py_Register_page otherwise it returns None. Note that
for a \ref py_MemoryAccess_page all information about LEA are lost at this level.

- <b>\ref py_SYMBOLIC_page getType(void)</b><br>
Returns the type of the symbolic expression.<br>
e.g: `SYMBOLIC.REGISTER_EXPRESSION`

- <b>bool isMemory(void)</b><br>
Returns true if the expression is assigned to memory.

- <b>bool isRegister(void)</b><br>
Returns true if the expression is assigned to a register.

- <b>bool isSymbolized(void)</b><br>
Returns true if the expression contains a symbolic variable.

- <b>bool isTainted(void)</b><br>
Returns true if the expression is tainted.

- <b>void setAst(\ref py_AstNode_page node)</b><br>
Sets a root node.

- <b>void setComment(string comment)</b><br>
Sets a comment to the symbolic expression.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! SymbolicExpression destructor.
      void SymbolicExpression_dealloc(PyObject* self) {
        std::cout << std::flush;
        PySymbolicExpression_AsSymbolicExpression(self) = nullptr; // decref the shared_ptr
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static PyObject* SymbolicExpression_getAst(PyObject* self, PyObject* noarg) {
        try {
          return PyAstNode(PySymbolicExpression_AsSymbolicExpression(self)->getAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_getComment(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PySymbolicExpression_AsSymbolicExpression(self)->getComment().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_getDisassembly(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("s", PySymbolicExpression_AsSymbolicExpression(self)->getDisassembly().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_getId(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUsize(PySymbolicExpression_AsSymbolicExpression(self)->getId());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_getNewAst(PyObject* self, PyObject* noarg) {
        try {
          return PyAstNode(PySymbolicExpression_AsSymbolicExpression(self)->getNewAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_getOrigin(PyObject* self, PyObject* noarg) {
        try {
          if (PySymbolicExpression_AsSymbolicExpression(self)->isMemory())
            return PyMemoryAccess(PySymbolicExpression_AsSymbolicExpression(self)->getOriginMemory());

          else if (PySymbolicExpression_AsSymbolicExpression(self)->isRegister())
            return PyRegister(PySymbolicExpression_AsSymbolicExpression(self)->getOriginRegister());

          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PySymbolicExpression_AsSymbolicExpression(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_isMemory(PyObject* self, PyObject* noarg) {
        try {
          if (PySymbolicExpression_AsSymbolicExpression(self)->isMemory() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_isRegister(PyObject* self, PyObject* noarg) {
        try {
          if (PySymbolicExpression_AsSymbolicExpression(self)->isRegister() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_isSymbolized(PyObject* self, PyObject* noarg) {
        try {
          if (PySymbolicExpression_AsSymbolicExpression(self)->isSymbolized() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_isTainted(PyObject* self, PyObject* noarg) {
        try {
          if (PySymbolicExpression_AsSymbolicExpression(self)->isTainted == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_setAst(PyObject* self, PyObject* node) {
        try {
          if (!PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "SymbolicExpression::setAst(): Expected a AstNode as argument.");
          PySymbolicExpression_AsSymbolicExpression(self)->setAst(PyAstNode_AsAstNode(node));
          Py_INCREF(Py_None);
        return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* SymbolicExpression_setComment(PyObject* self, PyObject* comment) {
        try {
          if (!PyStr_Check(comment))
            return PyErr_Format(PyExc_TypeError, "SymbolicExpression::setComment(): Expected a string as argument.");
          PySymbolicExpression_AsSymbolicExpression(self)->setComment(PyStr_AsString(comment));
          Py_INCREF(Py_None);
          return Py_None;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      #if !defined(IS_PY3_8) || !IS_PY3_8
      static int SymbolicExpression_print(PyObject* self, void* io, int s) {
        std::cout << PySymbolicExpression_AsSymbolicExpression(self);
        return 0;
      }
      #endif


      static PyObject* SymbolicExpression_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PySymbolicExpression_AsSymbolicExpression(self);
          return PyStr_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int SymbolicExpression_init(AstNode_Object *self, PyObject *args, PyObject *kwds) {
        return 0;
      }


      static PyObject* SymbolicExpression_new(PyTypeObject* type, PyObject* args, PyObject* kwds) {
        return type->tp_alloc(type, 0);
      }


      //! SymbolicExpression methods.
      PyMethodDef SymbolicExpression_callbacks[] = {
        {"getAst",            SymbolicExpression_getAst,            METH_NOARGS,    ""},
        {"getComment",        SymbolicExpression_getComment,        METH_NOARGS,    ""},
        {"getDisassembly",    SymbolicExpression_getDisassembly,    METH_NOARGS,    ""},
        {"getId",             SymbolicExpression_getId,             METH_NOARGS,    ""},
        {"getNewAst",         SymbolicExpression_getNewAst,         METH_NOARGS,    ""},
        {"getOrigin",         SymbolicExpression_getOrigin,         METH_NOARGS,    ""},
        {"getType",           SymbolicExpression_getType,           METH_NOARGS,    ""},
        {"isMemory",          SymbolicExpression_isMemory,          METH_NOARGS,    ""},
        {"isRegister",        SymbolicExpression_isRegister,        METH_NOARGS,    ""},
        {"isSymbolized",      SymbolicExpression_isSymbolized,      METH_NOARGS,    ""},
        {"isTainted",         SymbolicExpression_isTainted,         METH_NOARGS,    ""},
        {"setAst",            SymbolicExpression_setAst,            METH_O,         ""},
        {"setComment",        SymbolicExpression_setComment,        METH_O,         ""},
        {nullptr,             nullptr,                              0,              nullptr}
      };


      PyTypeObject SymbolicExpression_Type = {
        PyVarObject_HEAD_INIT(&PyType_Type, 0)
        "SymbolicExpression",                       /* tp_name */
        sizeof(SymbolicExpression_Object),          /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)SymbolicExpression_dealloc,     /* tp_dealloc */
        #if IS_PY3_8
        0,                                          /* tp_vectorcall_offset */
        #else
        (printfunc)SymbolicExpression_print,        /* tp_print */
        #endif
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        (reprfunc)SymbolicExpression_str,           /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        (reprfunc)SymbolicExpression_str,           /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "SymbolicExpression objects",               /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        SymbolicExpression_callbacks,               /* tp_methods */
        0,                                          /* tp_members */
        0,                                          /* tp_getset */
        0,                                          /* tp_base */
        0,                                          /* tp_dict */
        0,                                          /* tp_descr_get */
        0,                                          /* tp_descr_set */
        0,                                          /* tp_dictoffset */
        (initproc)SymbolicExpression_init,          /* tp_init */
        0,                                          /* tp_alloc */
        (newfunc)SymbolicExpression_new,            /* tp_new */
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


      PyObject* PySymbolicExpression(const triton::engines::symbolic::SharedSymbolicExpression& symExpr) {
        if (symExpr == nullptr) {
          Py_INCREF(Py_None);
          return Py_None;
        }

        PyType_Ready(&SymbolicExpression_Type);
        auto* object = (triton::bindings::python::SymbolicExpression_Object*)PyObject_CallObject((PyObject*)&SymbolicExpression_Type, nullptr);
        if (object != NULL) {
          object->symExpr = symExpr;
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
