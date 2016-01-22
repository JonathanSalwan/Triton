//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>
#include <symbolicExpression.hpp>



/*! \page py_SymbolicExpression_page SymbolicExpression
    \brief [**python api**] All information about the SymbolicExpression python object.

\tableofcontents

\section py_SymbolicExpression_description Description
<hr>

This object is used to represent a symbolic expression.

~~~~~~~~~~~~~{.py}
>>> from triton import *

>>> setArchitecture(ARCH.X86_64)

>>> opcodes = "\x48\x31\xD0"
>>> inst = Instruction()

>>> inst.setOpcodes(opcodes)
>>> inst.setAddress(0x400000)
>>> inst.updateContext(Register(REG.RAX, 12345));
>>> inst.updateContext(Register(REG.RDX, 67890));

>>> processing(inst)

>>> print inst
400000: xor rax, rdx

>>> for expr in inst.getSymbolicExpressions():
...     print expr
...
#0 = (bvxor ((_ extract 63 0) (_ bv12345 64)) ((_ extract 63 0) (_ bv67890 64))) ; XOR operation
#1 = (_ bv0 1) ; Clears carry flag
#2 = (_ bv0 1) ; Clears overflow flag
#3 = (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) [... skipped ...] ; Parity flag
#4 = (ite (= ((_ extract 63 63) #0) (_ bv1 1)) (_ bv1 1) (_ bv0 1)) ; Sign flag
#5 = (ite (= ((_ extract 63 0) #0) (_ bv0 64)) (_ bv1 1) (_ bv0 1)) ; Zero flag
#6 = (_ bv4194307 64) ; Program Counter

>>> expr_1 = inst.getSymbolicExpressions()[0]
>>> expr_1
<SymbolicExpression object at 0x7f93ddeb3b40>
>>> print expr_1
#0 = (bvxor ((_ extract 63 0) (_ bv12345 64)) ((_ extract 63 0) (_ bv67890 64))) ; XOR operation

>>> print expr_1.getId()
0

>>> ast = expr_1.getAst()
>>> ast
<SmtAstNode object at 0x7f93ddeb3c00>
>>> print ast
(bvxor ((_ extract 63 0) (_ bv12345 64)) ((_ extract 63 0) (_ bv67890 64)))

>>> expr_1.isMem()
False

>>> expr_1.isReg()
True

>>> print expr_1.getOriginRegister()
rax:64 bv[63..0]
~~~~~~~~~~~~~

\section SymbolicExpression_py_api Python API - Methods of the SymbolicExpression class
<hr>

- **getAst(void)**<br>
Returns the SMT AST root node of the symbolic expression as \ref py_SmtAstNode_page. This is the semantics.

- **getComment(void)**<br>
Returns the symbolic expression's comment as string if exists.

- **getId(void)**<br>
Returns the symbolic expression's id as integer. This id is always unique.<br>
e.g: `2387`

- **getKind(void)**<br>
Returns the symbolic expression's kind as \ref py_SYMEXPR_page.<br>
e.g: `SYMEXPR.REG`

- **getNewAst(void)**<br>
Returns a new SMT AST root node of the symbolic expression as \ref py_SmtAstNode_page. This new instance is a duplicate of the original node and may be changed without changing the original semantics.

- **getOriginAddress(void)**<br>
Returns the origin memory address if `isMem()` is equal to `True`, `0` otherwise. This address represents the target assignment.

- **getOriginRegister(void)**<br>
Returns the origin register if `isReg()` is equal `True`, `REG.INVALID` otherwise. This register represents the target assignment.

- **isMem(void)**<br>
Returns true if the expression is assigned to a memory.

- **isReg(void)**<br>
Returns true if the expression is assigned to a register.

- **isTainted(void)**<br>
Returns true if the expression is tainted.

- **setAst(\ref py_SmtAstNode_page node)**<br>
Sets a root node.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! SymbolicExpression's Destructor.
      void SymbolicExpression_dealloc(PyObject* self) {
        Py_DECREF(self);
      }


      static PyObject* SymbolicExpression_getAst(PyObject* self, PyObject* noarg) {
        return PySmtAstNode(PySymbolicExpression_AsSymbolicExpression(self)->getAst());
      }


      static PyObject* SymbolicExpression_getComment(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("s", PySymbolicExpression_AsSymbolicExpression(self)->getComment().c_str());
      }


      static PyObject* SymbolicExpression_getId(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PySymbolicExpression_AsSymbolicExpression(self)->getId());
      }


      static PyObject* SymbolicExpression_getKind(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PySymbolicExpression_AsSymbolicExpression(self)->getKind());
      }


      static PyObject* SymbolicExpression_getNewAst(PyObject* self, PyObject* noarg) {
        return PySmtAstNode(PySymbolicExpression_AsSymbolicExpression(self)->getNewAst());
      }


      static PyObject* SymbolicExpression_getOriginAddress(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint(PySymbolicExpression_AsSymbolicExpression(self)->getOriginAddress());
      }


      static PyObject* SymbolicExpression_getOriginRegister(PyObject* self, PyObject* noarg) {
        return PyRegisterOperand(PySymbolicExpression_AsSymbolicExpression(self)->getOriginRegister());
      }


      static PyObject* SymbolicExpression_isMem(PyObject* self, PyObject* noarg) {
        if (PySymbolicExpression_AsSymbolicExpression(self)->isMem() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* SymbolicExpression_isReg(PyObject* self, PyObject* noarg) {
        if (PySymbolicExpression_AsSymbolicExpression(self)->isReg() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* SymbolicExpression_isTainted(PyObject* self, PyObject* noarg) {
        if (PySymbolicExpression_AsSymbolicExpression(self)->isTainted == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* SymbolicExpression_setAst(PyObject* self, PyObject* node) {
        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "setAst(): expected a SmtAstNode as argument");
        PySymbolicExpression_AsSymbolicExpression(self)->setAst(PySmtAstNode_AsSmtAstNode(node));
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* SymbolicExpression_str(SymbolicExpression_Object *obj) {
        std::stringstream str;
        str << obj->symExpr;
        return PyString_FromFormat("%s", str.str().c_str());
      }


      //! SymbolicExpression's methods.
      PyMethodDef SymbolicExpression_callbacks[] = {
        {"getAst",            SymbolicExpression_getAst,            METH_NOARGS,    ""},
        {"getComment",        SymbolicExpression_getComment,        METH_NOARGS,    ""},
        {"getId",             SymbolicExpression_getId,             METH_NOARGS,    ""},
        {"getKind",           SymbolicExpression_getKind,           METH_NOARGS,    ""},
        {"getNewAst",         SymbolicExpression_getNewAst,         METH_NOARGS,    ""},
        {"getOriginAddress",  SymbolicExpression_getOriginAddress,  METH_NOARGS,    ""},
        {"getOriginRegister", SymbolicExpression_getOriginRegister, METH_NOARGS,    ""},
        {"isMem",             SymbolicExpression_isMem,             METH_NOARGS,    ""},
        {"isReg",             SymbolicExpression_isReg,             METH_NOARGS,    ""},
        {"isTainted",         SymbolicExpression_isTainted,         METH_NOARGS,    ""},
        {"setAst",            SymbolicExpression_setAst,            METH_O,         ""},
        {nullptr,             nullptr,                              0,              nullptr}
      };


      PyTypeObject SymbolicExpression_Type = {
          PyObject_HEAD_INIT(&PyType_Type)
          0,                                          /* ob_size*/
          "SymbolicExpression",                       /* tp_name*/
          sizeof(SymbolicExpression_Object),          /* tp_basicsize*/
          0,                                          /* tp_itemsize*/
          (destructor)SymbolicExpression_dealloc,     /* tp_dealloc*/
          0,                                          /* tp_print*/
          0,                                          /* tp_getattr*/
          0,                                          /* tp_setattr*/
          0,                                          /* tp_compare*/
          0,                                          /* tp_repr*/
          0,                                          /* tp_as_number*/
          0,                                          /* tp_as_sequence*/
          0,                                          /* tp_as_mapping*/
          0,                                          /* tp_hash */
          0,                                          /* tp_call*/
          (reprfunc)SymbolicExpression_str,           /* tp_str*/
          0,                                          /* tp_getattro*/
          0,                                          /* tp_setattro*/
          0,                                          /* tp_as_buffer*/
          Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
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
          0,                                          /* tp_init */
          0,                                          /* tp_alloc */
          0,                                          /* tp_new */
      };


      PyObject* PySymbolicExpression(triton::engines::symbolic::SymbolicExpression* symExpr) {
        SymbolicExpression_Object *object;

        if (symExpr == nullptr)
          return PyErr_Format(PyExc_TypeError, "PySymbolicExpression(): symExpr cannot be null.");

        PyType_Ready(&SymbolicExpression_Type);
        object = PyObject_NEW(SymbolicExpression_Object, &SymbolicExpression_Type);
        if (object != NULL)
          object->symExpr = symExpr;

        return (PyObject* )object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
