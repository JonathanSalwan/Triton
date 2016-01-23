//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <z3++.h>

#include <pythonObjects.hpp>
#include <pythonXFunctions.hpp>
#include <pythonUtils.hpp>
#include <smt2lib.hpp>



/*! \page py_SmtAstNode_page SmtAstNode
    \brief [**python api**] All information about the SmtAstNode python object.

\tableofcontents

\section py_SmtAstNode_description Description
<hr>

This object is used to represent each node of the SMT's AST.

~~~~~~~~~~~~~{.py}
>>> node = bvadd(bv(1, 8), bvxor(bv(10, 8), bv(20, 8)))
>>> print type(node)
<type 'SmtAstNode'>

>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

# Python's opertors overloaded

>>> a = bv(1, 8)
>>> b = bv(2, 8)
>>> c = (a & ~b) | (~a & b)
>>> print c
(bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))
~~~~~~~~~~~~~

\section SmtAstNode_py_api Python API - Methods of the SmtAstNode class
<hr>

- **getBitvectorSize(void)**<br>
Returns the expression's size.

- **getChilds(void)**<br>
Returns the list of the childs as \ref py_SmtAstNode_page.

- **getHash(void)**<br>
Returns the hash (signature) of the AST as float.

- **getKind(void)**<br>
Returns the kind of the node as \ref py_SMT_AST_NODE_page.<br>
e.g: `SMT_AST_NODE.BVADD`

- **getValue(void)**<br>
Returns the node's value as integer or string (it depends of the kind). For example if the node's kind is `decimal`, the value is an integer.

- **setChild(integer index, SmtAstNode node)**<br>
Replaces a child node.

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! SmtAstNode's Destructor.
      void SmtAstNode_dealloc(PyObject* self) {
        Py_DECREF(self);
      }


      static PyObject* SmtAstNode_getBitvectorSize(PyObject* self, PyObject* noarg) {
        try {
          return Py_BuildValue("k", PySmtAstNode_AsSmtAstNode(self)->getBitvectorSize());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        catch (const z3::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.msg());
        }
      }


      static PyObject* SmtAstNode_getChilds(PyObject* self, PyObject* noarg) {
        PyObject* childs;
        triton::smt2lib::smtAstAbstractNode *node = PySmtAstNode_AsSmtAstNode(self);

        triton::__uint size = node->getChilds().size();
        childs = xPyList_New(size);
        for (triton::__uint index = 0; index < size; index++)
          PyList_SetItem(childs, index, PySmtAstNode(node->getChilds()[index]));

        return childs;
      }


      static PyObject* SmtAstNode_getHash(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint512(PySmtAstNode_AsSmtAstNode(self)->hash(1));
      }


      static PyObject* SmtAstNode_getKind(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", PySmtAstNode_AsSmtAstNode(self)->getKind());
      }


      static PyObject* SmtAstNode_getValue(PyObject* self, PyObject* noarg) {
        triton::smt2lib::smtAstAbstractNode *node = PySmtAstNode_AsSmtAstNode(self);

        if (node->getKind() == triton::smt2lib::DECIMAL_NODE)
          return PyLong_FromUint128(reinterpret_cast<triton::smt2lib::smtAstDecimalNode *>(node)->getValue());

        else if (node->getKind() == triton::smt2lib::STRING_NODE)
          return Py_BuildValue("s", reinterpret_cast<triton::smt2lib::smtAstStringNode *>(node)->getValue().c_str());

        else if (node->getKind() == triton::smt2lib::REFERENCE_NODE)
          return PyLong_FromUint(reinterpret_cast<triton::smt2lib::smtAstReferenceNode *>(node)->getValue());

        return PyErr_Format(PyExc_TypeError, "SmtAstNode.getValue() - Cannot use getValue() on this kind of node");
      }


      static PyObject* SmtAstNode_setChild(PyObject* self, PyObject* args) {
        PyObject* index = nullptr;
        PyObject* node = nullptr;
        triton::__uint i;
        triton::smt2lib::smtAstAbstractNode *dst, *src;

        PyArg_ParseTuple(args, "|OO", &index, &node);

        if (index == nullptr || (!PyLong_Check(index) && !PyInt_Check(index)))
          return PyErr_Format(PyExc_TypeError, "setChild(): expected an index (integer) as first argument");

        if (node == nullptr || !PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "setChild(): expected a SmtAstNode as second argument");

        i = PyLong_AsUint(index);
        src = PySmtAstNode_AsSmtAstNode(node);
        dst = PySmtAstNode_AsSmtAstNode(self);
        if (i >= dst->getChilds().size())
          return PyErr_Format(PyExc_TypeError, "setChild(): index out-of-range");

        dst->getChilds()[i] = src;

        Py_RETURN_TRUE;
      }


      static int SmtAstNode_cmp(SmtAstNode_Object* a, SmtAstNode_Object* b) {
        return !(a->node->hash(1) == b->node->hash(1));
      }


      static PyObject* SmtAstNode_str(SmtAstNode_Object* obj) {
        std::stringstream str;
        str << obj->node;
        return PyString_FromFormat("%s", str.str().c_str());
      }


      static PyObject* SmtAstNode_operatorAdd(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvadd(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorSub(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvsub(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorMul(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvmul(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorDiv(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvsdiv(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorRem(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvsrem(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorMod(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvsmod(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorNeg(PyObject* node) {
        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as argument");
        return PySmtAstNode(smt2lib::bvneg(PySmtAstNode_AsSmtAstNode(node)));
      }


      static PyObject* SmtAstNode_operatorNot(PyObject* node) {
        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as argument");
        return PySmtAstNode(smt2lib::bvnot(PySmtAstNode_AsSmtAstNode(node)));
      }


      static PyObject* SmtAstNode_operatorShl(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvshl(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorShr(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvlshr(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorAnd(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvand(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorXor(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvxor(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      static PyObject* SmtAstNode_operatorOr(PyObject* self, PyObject* other) {
        if (!PySmtAstNode_Check(self) || !PySmtAstNode_Check(other))
          return PyErr_Format(PyExc_TypeError, "operator(): expected a SmtAstNode as arguments");
        return PySmtAstNode(smt2lib::bvor(PySmtAstNode_AsSmtAstNode(self), PySmtAstNode_AsSmtAstNode(other)));
      }


      //! SmtAstNode's methods.
      PyMethodDef SmtAstNode_callbacks[] = {
        {"getBitvectorSize",  SmtAstNode_getBitvectorSize,  METH_NOARGS,     ""},
        {"getChilds",         SmtAstNode_getChilds,         METH_NOARGS,     ""},
        {"getHash",           SmtAstNode_getHash,           METH_NOARGS,     ""},
        {"getKind",           SmtAstNode_getKind,           METH_NOARGS,     ""},
        {"getValue",          SmtAstNode_getValue,          METH_NOARGS,     ""},
        {"setChild",          SmtAstNode_setChild,          METH_VARARGS,    ""},
        {nullptr,             nullptr,                      0,               nullptr}
      };


      PyNumberMethods SmtAstNode_NumberMethods = {
        SmtAstNode_operatorAdd,                     /* nb_add */
        SmtAstNode_operatorSub,                     /* nb_subtract */
        SmtAstNode_operatorMul,                     /* nb_multiply */
        SmtAstNode_operatorDiv,                     /* nb_divide */
        SmtAstNode_operatorRem,                     /* nb_remainder */
        SmtAstNode_operatorMod,                     /* nb_divmod */
        0,                                          /* nb_power */
        SmtAstNode_operatorNeg,                     /* nb_negative */
        0,                                          /* nb_positive */
        0,                                          /* nb_absolute */
        0,                                          /* nb_nonzero */
        SmtAstNode_operatorNot,                     /* nb_invert */
        SmtAstNode_operatorShl,                     /* nb_lshift */
        SmtAstNode_operatorShr,                     /* nb_rshift */
        SmtAstNode_operatorAnd,                     /* nb_and */
        SmtAstNode_operatorXor,                     /* nb_xor */
        SmtAstNode_operatorOr,                      /* nb_or */
        0,                                          /* nb_coerce */
        0,                                          /* nb_int */
        0,                                          /* nb_long */
        0,                                          /* nb_float */
        0,                                          /* nb_oct */
        0,                                          /* nb_hex */
        SmtAstNode_operatorAdd,                     /* nb_inplace_add */
        SmtAstNode_operatorSub,                     /* nb_inplace_subtract */
        SmtAstNode_operatorMul,                     /* nb_inplace_multiply */
        SmtAstNode_operatorDiv,                     /* nb_inplace_divide */
        SmtAstNode_operatorRem,                     /* nb_inplace_remainder */
        0,                                          /* nb_inplace_power */
        SmtAstNode_operatorShl,                     /* nb_inplace_lshift */
        SmtAstNode_operatorShr,                     /* nb_inplace_rshift */
        SmtAstNode_operatorAnd,                     /* nb_inplace_and */
        SmtAstNode_operatorXor,                     /* nb_inplace_xor */
        SmtAstNode_operatorOr,                      /* nb_inplace_or */
        0,                                          /* nb_floor_divide */
        0,                                          /* nb_true_divide */
        0,                                          /* nb_inplace_floor_divide */
        0,                                          /* nb_inplace_true_divide */
        0,                                          /* nb_index */
      };


      PyTypeObject SmtAstNode_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size*/
        "SmtAstNode",                               /* tp_name*/
        sizeof(SmtAstNode_Object),                  /* tp_basicsize*/
        0,                                          /* tp_itemsize*/
        (destructor)SmtAstNode_dealloc,             /* tp_dealloc*/
        0,                                          /* tp_print*/
        0,                                          /* tp_getattr*/
        0,                                          /* tp_setattr*/
        (cmpfunc)SmtAstNode_cmp,                    /* tp_compare*/
        0,                                          /* tp_repr*/
        &SmtAstNode_NumberMethods,                  /* tp_as_number*/
        0,                                          /* tp_as_sequence*/
        0,                                          /* tp_as_mapping*/
        0,                                          /* tp_hash */
        0,                                          /* tp_call*/
        (reprfunc)SmtAstNode_str,                   /* tp_str*/
        0,                                          /* tp_getattro*/
        0,                                          /* tp_setattro*/
        0,                                          /* tp_as_buffer*/
        Py_TPFLAGS_DEFAULT,                         /* tp_flags*/
        "SmtAstNode objects",                       /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        SmtAstNode_callbacks,                       /* tp_methods */
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


      PyObject* PySmtAstNode(triton::smt2lib::smtAstAbstractNode* node) {
        SmtAstNode_Object *object;

        if (node == nullptr)
          return PyErr_Format(PyExc_TypeError, "PySmtAstNode(): The node cannot be null.");

        PyType_Ready(&SmtAstNode_Type);
        object = PyObject_NEW(SmtAstNode_Object, &SmtAstNode_Type);
        if (object != NULL)
          object->node = node;

        return (PyObject* )object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
