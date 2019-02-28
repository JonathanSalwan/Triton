//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/ast.hpp>
#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>



/* setup doctest context

>>> from triton import TritonContext, ARCH
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

*/

/*! \page py_AstNode_page AstNode
    \brief [**python api**] All information about the AstNode python object.

\tableofcontents

\section py_AstNode_description Description
<hr>

This object is used to represent each AST node of an expression.

~~~~~~~~~~~~~{.py}
>>> astCtxt = ctxt.getAstContext()
>>> node = astCtxt.bvadd(astCtxt.bv(1, 8), astCtxt.bvxor(astCtxt.bv(10, 8), astCtxt.bv(20, 8)))
>>> print(node)
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

# Python's opertors overloaded

>>> a = astCtxt.bv(1, 8)
>>> b = astCtxt.bv(2, 8)
>>> c = (a & ~b) | (~a & b)
>>> print(c)
(bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))

~~~~~~~~~~~~~

\section AstNode_py_api Python API - Methods of the AstNode class
<hr>

- <b>bool equalTo(\ref py_AstNode_page)</b><br>
Compares the current tree to another one.

- <b>integer evaluate(void)</b><br>
Evaluates the tree and returns its value.

- <b>integer getBitvectorMask(void)</b><br>
Returns the mask of the node vector according to its size.<br>
e.g: `0xffffffff`

- <b>integer getBitvectorSize(void)</b><br>
Returns the node vector size.

- <b>[\ref py_AstNode_page, ...] getChildren(void)</b><br>
Returns the list of child nodes.

- <b>integer getHash(void)</b><br>
Returns the hash (signature) of the AST .

- <b>integer getInteger(void)</b><br>
Returns the integer of the node. Only available on `INTEGER_NODE`, raises an exception otherwise.

- <b>[\ref py_AstNode_page, ...] getParents(void)</b><br>
Returns the parents list nodes. The list is empty if there is still no parent defined.

- <b>string getString(void)</b><br>
Returns the string of the node. Only available on `STRING_NODE`, raises an exception otherwise.

- <b>\ref py_SymbolicExpression_page getSymbolicExpression(void)</b><br>
Returns the symbolic expression of the node. Only available on `REFERENCE_NODE`, raises an exception otherwise.

- <b>\ref py_SymbolicVariable_page getSymbolicVariable(void)</b><br>
Returns the symbolic variable of the node. Only available on `VARIABLE_NODE`, raises an exception otherwise.

- <b>\ref py_AST_NODE_page getType(void)</b><br>
Returns the kind of the node.<br>
e.g: `AST_NODE.BVADD`

- <b>bool isLogical(void)</b><br>
Returns true if it's a logical node.
e.g: `AST_NODE.EQUAL`, `AST_NODE.LNOT`, `AST_NODE.LAND`...

- <b>bool isSigned(void)</b><br>
According to the size of the expression, returns true if the MSB is 1.

- <b>bool isSymbolized(void)</b><br>
Returns true if the tree (and its sub-trees) contains a symbolic variable.

- <b>void setChild(integer index, \ref py_AstNode_page node)</b><br>
Replaces a child node.

\section AstNode_operator_py_api Python API - Operators
<hr>

As we can not overload all AST's operators only these following operators are overloaded:

Python's Operator | e.g: SMT2-Lib format
------------------|---------------------
a + b             | (bvadd a b)
a - b             | (bvsub a b)
a \* b            | (bvmul a b)
a / b             | (bvudiv a b)
a \| b            | (bvor a b)
a & b             | (bvand a b)
a ^ b             | (bvxor a b)
a % b             | (bvurem a b)
a << b            | (bvshl a b)
a \>> b           | (bvlshr a b)
~a                | (bvnot a)
-a                | (bvneg a)
a == b            | (= a b)
a != b            | (not (= a b))
a <= b            | (bvule a b)
a >= b            | (bvuge a b)
a < b             | (bvult a b)
a > b             | (bvugt a b)

*/



namespace triton {
  namespace bindings {
    namespace python {

      //! AstNode destructor.
      void AstNode_dealloc(PyObject* self) {
        std::cout << std::flush;
        PyAstNode_AsAstNode(self) = nullptr; // decref the shared_ptr
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static PyObject* AstNode_equalTo(PyObject* self, PyObject* other) {
        try {
          if (other == nullptr || !PyAstNode_Check(other))
            return PyErr_Format(PyExc_TypeError, "AstNode::equalTo(): Expected a AstNode as argument.");

          if (PyAstNode_AsAstNode(self)->equalTo(PyAstNode_AsAstNode(other)))
            Py_RETURN_TRUE;

          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_evaluate(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyAstNode_AsAstNode(self)->evaluate());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getBitvectorMask(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyAstNode_AsAstNode(self)->getBitvectorMask());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getBitvectorSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyAstNode_AsAstNode(self)->getBitvectorSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getChildren(PyObject* self, PyObject* noarg) {
        try {
          PyObject* children;
          triton::ast::SharedAbstractNode node = PyAstNode_AsAstNode(self);

          triton::usize size = node->getChildren().size();
          children = xPyList_New(size);
          for (triton::usize index = 0; index < size; index++)
            PyList_SetItem(children, index, PyAstNode(node->getChildren()[index]));

          return children;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getHash(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint512(PyAstNode_AsAstNode(self)->hash(1));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getInteger(PyObject* self, PyObject* noarg) {
        triton::ast::SharedAbstractNode node = PyAstNode_AsAstNode(self);

        if (node->getType() != triton::ast::INTEGER_NODE)
          return PyErr_Format(PyExc_TypeError, "AstNode::getInteger(): Only available on INTEGER_NODE type.");

        try {
          return PyLong_FromUint512(reinterpret_cast<triton::ast::IntegerNode*>(node.get())->getInteger());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getParents(PyObject* self, PyObject* noarg) {
        try {
          PyObject* ret = nullptr;
          auto parents = PyAstNode_AsAstNode(self)->getParents();
          ret = xPyList_New(parents.size());
          triton::uint32 index = 0;
          for (auto& sp : parents)
            PyList_SetItem(ret, index++, PyAstNode(sp));
          return ret;
          }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getString(PyObject* self, PyObject* noarg) {
        triton::ast::SharedAbstractNode node = PyAstNode_AsAstNode(self);

        if (node->getType() != triton::ast::STRING_NODE)
          return PyErr_Format(PyExc_TypeError, "AstNode::getString(): Only available on STRING_NODE type.");

        try {
          return Py_BuildValue("s", reinterpret_cast<triton::ast::StringNode*>(node.get())->getString().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getSymbolicExpression(PyObject* self, PyObject* noarg) {
        triton::ast::SharedAbstractNode node = PyAstNode_AsAstNode(self);

        if (node->getType() != triton::ast::REFERENCE_NODE)
          return PyErr_Format(PyExc_TypeError, "AstNode::getSymbolicExpression(): Only available on REFERENCE_NODE type.");

        try {
          return PySymbolicExpression(reinterpret_cast<triton::ast::ReferenceNode*>(node.get())->getSymbolicExpression());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getSymbolicVariable(PyObject* self, PyObject* noarg) {
        triton::ast::SharedAbstractNode node = PyAstNode_AsAstNode(self);

        if (node->getType() != triton::ast::VARIABLE_NODE)
          return PyErr_Format(PyExc_TypeError, "AstNode::getSymbolicVariable(): Only available on VARIABLE_NODE type.");

        try {
          return PySymbolicVariable(reinterpret_cast<triton::ast::VariableNode*>(node.get())->getSymbolicVariable());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_getType(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyAstNode_AsAstNode(self)->getType());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_isLogical(PyObject* self, PyObject* noarg) {
        try {
          if (PyAstNode_AsAstNode(self)->isLogical())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_isSigned(PyObject* self, PyObject* noarg) {
        try {
          if (PyAstNode_AsAstNode(self)->isSigned())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_isSymbolized(PyObject* self, PyObject* noarg) {
        try {
          if (PyAstNode_AsAstNode(self)->isSymbolized())
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_setChild(PyObject* self, PyObject* args) {
        try {
          PyObject* index = nullptr;
          PyObject* node = nullptr;
          triton::uint32 idx;
          triton::ast::SharedAbstractNode dst, src;

          PyArg_ParseTuple(args, "|OO", &index, &node);

          if (index == nullptr || (!PyLong_Check(index) && !PyInt_Check(index)))
            return PyErr_Format(PyExc_TypeError, "AstNode::setChild(): Expected an index (integer) as first argument.");

          if (node == nullptr || !PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "AstNode::setChild(): Expected a AstNode as second argument.");

          idx = PyLong_AsUint32(index);
          src = PyAstNode_AsAstNode(node);
          dst = PyAstNode_AsAstNode(self);
          dst->setChild(idx, src);
          dst->init();

          Py_RETURN_TRUE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static int AstNode_print(PyObject* self, void* io, int s) {
        std::cout << PyAstNode_AsAstNode(self);
        return 0;
      }


      #if !defined(IS_PY3) || !IS_PY3
      static int AstNode_cmp(PyObject* a, PyObject* b) {
        if (!PyAstNode_Check(a) || !PyAstNode_Check(b)) {
          PyErr_Format(
            PyExc_TypeError,
            "__cmp__ not supported between instances of '%.100s' and '%.100s'",
            a->ob_type->tp_name,
            b->ob_type->tp_name);
          return -1;
        }
        auto ha = PyAstNode_AsAstNode(a)->hash(1);
        auto hb = PyAstNode_AsAstNode(b)->hash(1);
        return (ha == hb ? 0 : (ha > hb ? 1 : -1));
      }
      #endif


      static PyObject* AstNode_str(PyObject* self) {
        try {
          std::stringstream str;
          str << PyAstNode_AsAstNode(self);
          return PyStr_FromFormat("%s", str.str().c_str());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorAdd(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvadd(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvadd(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvadd(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorAdd(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorSub(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvsub(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvsub(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvsub(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorSub(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorMul(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvmul(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvmul(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvmul(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorMul(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorDiv(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvudiv(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvudiv(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvudiv(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorDiv(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorRem(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvurem(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvurem(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvurem(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorMod(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorNeg(PyObject* node) {
        try {
          if (!PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorNeg(): Expected a AstNode as argument.");
          return PyAstNode(PyAstNode_AsAstNode(node)->getContext().bvneg(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorNot(PyObject* node) {
        try {
          if (!PyAstNode_Check(node))
            return PyErr_Format(PyExc_TypeError, "AstNode::operatorNot(): Expected a AstNode as argument.");
          return PyAstNode(PyAstNode_AsAstNode(node)->getContext().bvnot(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorShl(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvshl(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvshl(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvshl(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorShl(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorShr(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvlshr(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvlshr(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvlshr(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorShr(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorAnd(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvand(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvand(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvand(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorAnd(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorXor(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvxor(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvxor(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvxor(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorXor(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstNode_operatorOr(PyObject* self, PyObject* other) {
        try {
          #if IS_PY3
          if ((PyInt_Check(self) || PyLong_Check(self)) && PyAstNode_Check(other)) {
            auto& nother = PyAstNode_AsAstNode(other);
            auto& ast    = nother->getContext();
            auto  nself  = ast.bv(PyLong_AsUint512(self), nother->getBitvectorSize());
            return PyAstNode(ast.bvor(nself, nother));
          }

          if (PyAstNode_Check(self) && (PyInt_Check(other) || PyLong_Check(other))) {
            auto& nself  = PyAstNode_AsAstNode(self);
            auto& ast    = nself->getContext();
            auto  nother = ast.bv(PyLong_AsUint512(other), nself->getBitvectorSize());
            return PyAstNode(ast.bvor(nself, nother));
          }
          #endif

          if (PyAstNode_Check(self) && PyAstNode_Check(other))
            return PyAstNode(PyAstNode_AsAstNode(self)->getContext().bvor(PyAstNode_AsAstNode(self), PyAstNode_AsAstNode(other)));

          return PyErr_Format(PyExc_TypeError, "AstNode::operatorOr(): Expected a AstNode as arguments.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      #if !defined(IS_PY3) || !IS_PY3
      static int AstNode_coerce(PyObject** self, PyObject** other) {
        if (PyLong_Check(*other) || PyInt_Check(*other)) {
          triton::uint512 value = PyLong_AsUint512(*other);
          triton::uint32 size   = PyAstNode_AsAstNode(*self)->getBitvectorSize();
          if (size) {
            *other = PyAstNode(PyAstNode_AsAstNode(*self)->getContext().bv(value, size));
            Py_INCREF(*self);
            return 0;
          }
        }
        return 1;
      }
      #endif


      static PyObject* AstNode_richcompare(PyObject* self, PyObject* other, int op) {
        PyObject* result = nullptr;

        if (PyLong_Check(other) || PyInt_Check(other)) {
          triton::uint512 value = PyLong_AsUint512(other);
          triton::uint32 size   = PyAstNode_AsAstNode(self)->getBitvectorSize();
          if (size)
            other = PyAstNode(PyAstNode_AsAstNode(self)->getContext().bv(value, size));
        }

        if (!PyAstNode_Check(other)) {
          result = Py_NotImplemented;
        }

        else {
          auto node1 = PyAstNode_AsAstNode(self);
          auto node2 = PyAstNode_AsAstNode(other);

          switch (op) {
            case Py_LT:
                result = PyAstNode(node1->getContext().bvult(node1, node2));
                break;
            case Py_LE:
                result = PyAstNode(node1->getContext().bvule(node1, node2));
                break;
            case Py_EQ:
                result = PyAstNode(node1->getContext().equal(node1, node2));
                break;
            case Py_NE:
                result = PyAstNode(node1->getContext().lnot(node1->getContext().equal(node1, node2)));
                break;
            case Py_GT:
                result = PyAstNode(node1->getContext().bvugt(node1, node2));
                break;
            case Py_GE:
                result = PyAstNode(node1->getContext().bvuge(node1, node2));
                break;
          }
        }

        Py_INCREF(result);
        return result;
      }


      static PyObject* AstNode_new(PyTypeObject* type, PyObject* args, PyObject* kwds) {
        return type->tp_alloc(type, 0);
      }


      static int AstNode_init(AstNode_Object* self, PyObject* args, PyObject* kwds) {
        return 0;
      }


      //! AstNode methods.
      PyMethodDef AstNode_callbacks[] = {
        {"equalTo",                 AstNode_equalTo,                METH_O,          ""},
        {"evaluate",                AstNode_evaluate,               METH_NOARGS,     ""},
        {"getBitvectorMask",        AstNode_getBitvectorMask,       METH_NOARGS,     ""},
        {"getBitvectorSize",        AstNode_getBitvectorSize,       METH_NOARGS,     ""},
        {"getChildren",             AstNode_getChildren,            METH_NOARGS,     ""},
        {"getHash",                 AstNode_getHash,                METH_NOARGS,     ""},
        {"getInteger",              AstNode_getInteger,             METH_NOARGS,     ""},
        {"getParents",              AstNode_getParents,             METH_NOARGS,     ""},
        {"getString",               AstNode_getString,              METH_NOARGS,     ""},
        {"getSymbolicExpression",   AstNode_getSymbolicExpression,  METH_NOARGS,     ""},
        {"getSymbolicVariable",     AstNode_getSymbolicVariable,    METH_NOARGS,     ""},
        {"getType",                 AstNode_getType,                METH_NOARGS,     ""},
        {"isLogical",               AstNode_isLogical,              METH_NOARGS,     ""},
        {"isSigned",                AstNode_isSigned,               METH_NOARGS,     ""},
        {"isSymbolized",            AstNode_isSymbolized,           METH_NOARGS,     ""},
        {"setChild",                AstNode_setChild,               METH_VARARGS,    ""},
        {nullptr,                   nullptr,                        0,               nullptr}
      };


      //! AstNode operator methods.
      PyNumberMethods AstNode_NumberMethods = {
        AstNode_operatorAdd,                        /* nb_add */
        AstNode_operatorSub,                        /* nb_subtract */
        AstNode_operatorMul,                        /* nb_multiply */
        #if !defined(IS_PY3) || !IS_PY3
        AstNode_operatorDiv,                        /* nb_divide */
        #endif
        AstNode_operatorRem,                        /* nb_remainder */
        0,                                          /* nb_divmod */
        0,                                          /* nb_power */
        AstNode_operatorNeg,                        /* nb_negative */
        0,                                          /* nb_positive */
        0,                                          /* nb_absolute */
        0,                                          /* nb_nonzero/nb_bool */
        AstNode_operatorNot,                        /* nb_invert */
        AstNode_operatorShl,                        /* nb_lshift */
        AstNode_operatorShr,                        /* nb_rshift */
        AstNode_operatorAnd,                        /* nb_and */
        AstNode_operatorXor,                        /* nb_xor */
        AstNode_operatorOr,                         /* nb_or */
        #if !defined(IS_PY3) || !IS_PY3
        AstNode_coerce,                             /* nb_coerce */
        #endif
        0,                                          /* nb_int */
        0,                                          /* nb_long/nb_reserved */
        0,                                          /* nb_float */
        #if !defined(IS_PY3) || !IS_PY3
        0,                                          /* nb_oct */
        0,                                          /* nb_hex */
        #endif
        AstNode_operatorAdd,                        /* nb_inplace_add */
        AstNode_operatorSub,                        /* nb_inplace_subtract */
        AstNode_operatorMul,                        /* nb_inplace_multiply */
        #if !defined(IS_PY3) || !IS_PY3
        AstNode_operatorDiv,                        /* nb_inplace_divide */
        #endif
        AstNode_operatorRem,                        /* nb_inplace_remainder */
        0,                                          /* nb_inplace_power */
        AstNode_operatorShl,                        /* nb_inplace_lshift */
        AstNode_operatorShr,                        /* nb_inplace_rshift */
        AstNode_operatorAnd,                        /* nb_inplace_and */
        AstNode_operatorXor,                        /* nb_inplace_xor */
        AstNode_operatorOr,                         /* nb_inplace_or */
        AstNode_operatorDiv,                        /* nb_floor_divide */
        AstNode_operatorDiv,                        /* nb_true_divide */
        AstNode_operatorDiv,                        /* nb_inplace_floor_divide */
        AstNode_operatorDiv,                        /* nb_inplace_true_divide */
        0,                                          /* nb_index */
        #if defined(IS_PY3) && IS_PY3
        0,                                          /* nb_matrix_multiply */
        0,                                          /* nb_inplace_matrix_multiply */
        #endif
      };


      PyTypeObject AstNode_Type = {
        PyVarObject_HEAD_INIT(&PyType_Type, 0)
        "AstNode",                                  /* tp_name */
        sizeof(AstNode_Object),                     /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)AstNode_dealloc,                /* tp_dealloc */
        (printfunc)AstNode_print,                   /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        #if defined(IS_PY3) && IS_PY3
        0,                                          /* tp_as_async */
        #else
        (cmpfunc)AstNode_cmp,                       /* tp_compare */
        #endif
        0,                                          /* tp_repr */
        &AstNode_NumberMethods,                     /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call*/
        (reprfunc)AstNode_str,                      /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "AstNode objects",                          /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        (richcmpfunc)AstNode_richcompare,           /* tp_richcompare */
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
        (initproc)AstNode_init,                     /* tp_init */
        0,                                          /* tp_alloc */
        (newfunc)AstNode_new,                       /* tp_new */
        0,                                          /* tp_free */
        0,                                          /* tp_is_gc */
        0,                                          /* tp_bases */
        0,                                          /* tp_mro */
        0,                                          /* tp_cache */
        0,                                          /* tp_subclasses */
        0,                                          /* tp_weaklist */
        (destructor)AstNode_dealloc,                /* tp_del */
        #if IS_PY3
        0,                                          /* tp_version_tag */
        0,                                          /* tp_finalize */
        #else
        0                                           /* tp_version_tag */
        #endif
      };


      PyObject* PyAstNode(const triton::ast::SharedAbstractNode& node) {
        if (node == nullptr) {
          Py_INCREF(Py_None);
          return Py_None;
        }

        PyType_Ready(&AstNode_Type);
        // Build the new object the python way (calling operator() on the type) as
        // it crash otherwise (certainly due to incorrect shared_ptr initialization).
        auto* object = (triton::bindings::python::AstNode_Object*)PyObject_CallObject((PyObject*) &AstNode_Type, nullptr);
        if (object != NULL) {
          object->node = node;
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
