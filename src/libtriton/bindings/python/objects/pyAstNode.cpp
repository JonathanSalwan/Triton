//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <z3++.h>

#include <ast.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>



/*! \page py_AstNode_page AstNode
    \brief [**python api**] All information about the AstNode python object.

\tableofcontents

\section py_AstNode_description Description
<hr>

This object is used to represent each AST node of an expression.

~~~~~~~~~~~~~{.py}
>>> node = bvadd(bv(1, 8), bvxor(bv(10, 8), bv(20, 8)))
>>> print type(node)
<type 'AstNode'>

>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

# Python's opertors overloaded

>>> a = bv(1, 8)
>>> b = bv(2, 8)
>>> c = (a & ~b) | (~a & b)
>>> print c
(bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))
~~~~~~~~~~~~~

\section AstNode_py_api Python API - Methods of the AstNode class
<hr>

- **evaluate(void)**<br>
Evaluates the tree and returns the value as integer.

- **getBitvectorMask(void)**<br>
Returns the mask of the node vector according to its size.<br>
e.g: `0xffffffff`

- **getBitvectorSize(void)**<br>
Returns the node vector size.

- **getChilds(void)**<br>
Returns the list of child nodes as \ref py_AstNode_page.

- **getHash(void)**<br>
Returns the hash (signature) of the AST as float.

- **getKind(void)**<br>
Returns the kind of the node as \ref py_AST_NODE_page.<br>
e.g: `AST_NODE.BVADD`

- **getParents(void)**<br>
Returns the parents list nodes as \ref py_AstNode_page. The list is empty if there is still no parent defined.

- **getValue(void)**<br>
Returns the node value as integer or string (it depends of the kind). For example if the kind of node is `decimal`, the value is an integer.

- **isSigned(void)**<br>
According to the size of the expression, returns true if the MSB is 1.

- **isSymbolized(void)**<br>
Returns true if the tree contains a symbolic variable.

- **setChild(integer index, AstNode node)**<br>
Replaces a child node.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! AstNode destructor.
      void AstNode_dealloc(PyObject* self) {
        std::cout << std::flush;
        Py_DECREF(self);
      }


      static PyObject* AstNode_evaluate(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyAstNode_AsAstNode(self)->evaluate());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getBitvectorMask(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyAstNode_AsAstNode(self)->getBitvectorMask());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getBitvectorSize(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("k", PyAstNode_AsAstNode(self)->getBitvectorSize());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getChilds(PyObject* self, PyObject* noarg) {
        try {
          PyObject* childs;
          triton::ast::AbstractNode *node = PyAstNode_AsAstNode(self);

          triton::__uint size = node->getChilds().size();
          childs = xPyList_New(size);
          for (triton::__uint index = 0; index < size; index++)
            PyList_SetItem(childs, index, PyAstNode(node->getChilds()[index]));

          return childs;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getHash(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyAstNode_AsAstNode(self)->hash(1));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getKind(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("k", PyAstNode_AsAstNode(self)->getKind());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getParents(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret = nullptr;
          std::set<triton::ast::AbstractNode*>& parents = PyAstNode_AsAstNode(self)->getParents();
          ret = xPyList_New(parents.size());
          triton::uint32 index = 0;
          for (std::set<triton::ast::AbstractNode*>::iterator it = parents.begin(); it != parents.end(); it++)
            PyList_SetItem(ret, index++, PyAstNode(*it));
          return ret;
          }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getValue(PyObject* self, PyObject* noarg) {
        try {
          triton::ast::AbstractNode *node = PyAstNode_AsAstNode(self);

          if (node->getKind() == triton::ast::DECIMAL_NODE)
            return PyLong_FromUint512(reinterpret_cast<triton::ast::DecimalNode *>(node)->getValue());

          else if (node->getKind() == triton::ast::REFERENCE_NODE)
            return PyLong_FromUint(reinterpret_cast<triton::ast::ReferenceNode *>(node)->getValue());

          else if (node->getKind() == triton::ast::STRING_NODE)
            return Py_BuildValue("s", reinterpret_cast<triton::ast::StringNode *>(node)->getValue().c_str());

          else if (node->getKind() == triton::ast::VARIABLE_NODE)
            return Py_BuildValue("s", reinterpret_cast<triton::ast::VariableNode *>(node)->getValue().c_str());

          return PyErr_Format(PyExc_TypeError, "AstNode::getValue(): Cannot use getValue() on this kind of node.");
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_isSigned(PyObject* self, PyObject* noarg) {
        try {
          if (PyAstNode_AsAstNode(self)->isSigned())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_isSymbolized(PyObject* self, PyObject* noarg) {
        try {
          if (PyAstNode_AsAstNode(self)->isSymbolized())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_setChild(PyObject* self, PyObject* args) {
        try {
          PyObject* index = nullptr;
          PyObject* node = nullptr;
          triton::__uint i;
          triton::ast::AbstractNode *dst, *src;

          PyArg_ParseTuple(args, "|OO", &index, &node);

          if (index == nullptr || (!PyLong_Check(index) && !PyInt_Check(index)))
            return PyErr_Format(PyExc_TypeError, "AstNode::setChild(): Expected an index (integer) as first argument.");

          if (node == nullptr || !PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "AstNode::setChild(): Expected a AstNode as second argument.");

          i = PyLong_AsUint(index);
          src = PyAstNode_AsAstNode(node);
          dst = PyAstNode_AsAstNode(self);
          dst->setChild(i, src);
          dst->init();

          Py_RETURN_TRUE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int AstNode_print(PyObject* self) {
        std::cout << PyAstNode_AsAstNode(self);
        return 0;
      }


      static int AstNode_cmp(AstNode_Object* a, AstNode_Object* b) {
        return !(a->node->hash(1) == b->node->hash(1));
      }


      static PyObject* AstNode_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyAstNode_AsAstNode(self);
          return PyString_FromFormat("%s", str.str().c_str());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorAdd(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorAdd(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvadd(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorSub(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorSub(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvsub(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorMul(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorMul(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvmul(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorDiv(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorDiv(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvsdiv(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorRem(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorRem(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvsrem(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorMod(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorMod(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvsmod(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorNeg(PyObject* node) {
        try {
          if (!PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorNeg(): Expected a AstNode as argument.");
          return PyAstNode(triton::ast::bvneg(PyAstNode_AsAstNode(node)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorNot(PyObject* node) {
        try {
          if (!PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorNot(): Expected a AstNode as argument.");
          return PyAstNode(triton::ast::bvnot(PyAstNode_AsAstNode(node)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorShl(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorShl(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvshl(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorShr(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorShr(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvlshr(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorAnd(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorAnd(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvand(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorXor(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorXor(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvxor(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorOr(PyObject* self, PyObject* other) {
        try {
          if (!PyAstNode_Check(self) || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorOr(): Expected a AstNode as arguments.");
          return PyAstNode(triton::ast::bvor(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int AstNode_coerce(PyObject** self, PyObject** other) {
        if (PyLong_Check(*other) || PyInt_Check(*other)) {
          triton::uint512 value = PyLong_AsUint512(*other);
          triton::__uint size   = PyAstNode_AsAstNode(*self)->getBitvectorSize();
          if (size) {
            *other = PyAstNode(triton::ast::bv(value, size));
            Py_INCREF(*self);
            return 0;
          }
        }
        return 1;
      }


      //! AstNode methods.
      PyMethodDef AstNode_callbacks[] = {
        {"evaluate",          AstNode_evaluate,          METH_NOARGS,     ""},
        {"getBitvectorMask",  AstNode_getBitvectorMask,  METH_NOARGS,     ""},
        {"getBitvectorSize",  AstNode_getBitvectorSize,  METH_NOARGS,     ""},
        {"getChilds",         AstNode_getChilds,         METH_NOARGS,     ""},
        {"getHash",           AstNode_getHash,           METH_NOARGS,     ""},
        {"getKind",           AstNode_getKind,           METH_NOARGS,     ""},
        {"getParents",        AstNode_getParents,        METH_NOARGS,     ""},
        {"getValue",          AstNode_getValue,          METH_NOARGS,     ""},
        {"isSigned",          AstNode_isSigned,          METH_NOARGS,     ""},
        {"isSymbolized",      AstNode_isSymbolized,      METH_NOARGS,     ""},
        {"setChild",          AstNode_setChild,          METH_VARARGS,    ""},
        {nullptr,             nullptr,                   0,               nullptr}
      };


      //! AstNode operator methods.
      PyNumberMethods AstNode_NumberMethods = {
        AstNode_operatorAdd,                        /* nb_add */
        AstNode_operatorSub,                        /* nb_subtract */
        AstNode_operatorMul,                        /* nb_multiply */
        AstNode_operatorDiv,                        /* nb_divide */
        AstNode_operatorRem,                        /* nb_remainder */
        AstNode_operatorMod,                        /* nb_divmod */
        0,                                          /* nb_power */
        AstNode_operatorNeg,                        /* nb_negative */
        0,                                          /* nb_positive */
        0,                                          /* nb_absolute */
        0,                                          /* nb_nonzero */
        AstNode_operatorNot,                        /* nb_invert */
        AstNode_operatorShl,                        /* nb_lshift */
        AstNode_operatorShr,                        /* nb_rshift */
        AstNode_operatorAnd,                        /* nb_and */
        AstNode_operatorXor,                        /* nb_xor */
        AstNode_operatorOr,                         /* nb_or */
        AstNode_coerce,                             /* nb_coerce */
        0,                                          /* nb_int */
        0,                                          /* nb_long */
        0,                                          /* nb_float */
        0,                                          /* nb_oct */
        0,                                          /* nb_hex */
        AstNode_operatorAdd,                        /* nb_inplace_add */
        AstNode_operatorSub,                        /* nb_inplace_subtract */
        AstNode_operatorMul,                        /* nb_inplace_multiply */
        AstNode_operatorDiv,                        /* nb_inplace_divide */
        AstNode_operatorRem,                        /* nb_inplace_remainder */
        0,                                          /* nb_inplace_power */
        AstNode_operatorShl,                        /* nb_inplace_lshift */
        AstNode_operatorShr,                        /* nb_inplace_rshift */
        AstNode_operatorAnd,                        /* nb_inplace_and */
        AstNode_operatorXor,                        /* nb_inplace_xor */
        AstNode_operatorOr,                         /* nb_inplace_or */
        0,                                          /* nb_floor_divide */
        0,                                          /* nb_true_divide */
        0,                                          /* nb_inplace_floor_divide */
        0,                                          /* nb_inplace_true_divide */
        0,                                          /* nb_index */
      };


      PyTypeObject AstNode_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size*/
        "AstNode",                                  /* tp_name*/
        sizeof(AstNode_Object),                     /* tp_basicsize*/
        0,                                          /* tp_itemsize*/
        (destructor)AstNode_dealloc,                /* tp_dealloc*/
        (printfunc)AstNode_print,                   /* tp_print*/
        0,                                          /* tp_getattr*/
        0,                                          /* tp_setattr*/
        (cmpfunc)AstNode_cmp,                       /* tp_compare*/
        0,                                          /* tp_repr*/
        &AstNode_NumberMethods,                     /* tp_as_number*/
        0,                                          /* tp_as_sequence*/
        0,                                          /* tp_as_mapping*/
        0,                                          /* tp_hash */
        0,                                          /* tp_call*/
        (reprfunc)AstNode_str,                      /* tp_str*/
        0,                                          /* tp_getattro*/
        0,                                          /* tp_setattro*/
        0,                                          /* tp_as_buffer*/
        Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
        "AstNode objects",                          /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        AstNode_callbacks,                          /* tp_methods */
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


      PyObject* PyAstNode(triton::ast::AbstractNode* node) {
        AstNode_Object* object;

        if (node == nullptr)
          return PyErr_Format(PyExc_TypeError, "PyAstNode(): The node cannot be null.");

        PyType_Ready(&AstNode_Type);
        object = PyObject_NEW(AstNode_Object, &AstNode_Type);
        if (object != NULL)
          object->node = node;

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
