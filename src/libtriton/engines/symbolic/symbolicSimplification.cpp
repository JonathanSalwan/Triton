//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <tritonToZ3Ast.hpp>
#include <z3Result.hpp>
#include <z3ToTritonAst.hpp>
#include <symbolicSimplification.hpp>

#ifdef TRITON_PYTHON_BINDINGS
  #include <pythonObjects.hpp>
  #include <pythonXFunctions.hpp>
#endif



/*! \page SMT_simplification_page SMT simplification passes
    \brief [**internal**] All information about the SMT simplification passes.

\tableofcontents
\section SMT_simplification_description Description
<hr>

Triton allows you to optimize your AST (See: \ref py_ast_page) just before the assignment to a register, a memory
or a volatile symbolic expression.

<p align="center"><img src="http://triton.quarkslab.com/files/simplification.png"/></p>

The record of a simplification pass is really straightforward. You have to record your simplification
callback using the triton::API::recordSimplificationCallback() function. Your simplification callback
must takes as unique parameter a pointer of triton::ast::AbstractNode and returns a pointer of
triton::ast::AbstractNode. Then, your callback will be called before every symbolic assignment.
Note that you can record several simplification callbacks or remove a specific callback using the
triton::API::removeSimplificationCallback() function.

\subsection SMT_simplification_triton Simplification via Triton's rules
<hr>

Below, a little example which replaces all \f$ A \oplus A \rightarrow A = 0\f$.

~~~~~~~~~~~~~{.cpp}
// Rule: if (bvxor x x) -> (_ bv0 x_size)
triton::ast::AbstractNode* xor_simplification(triton::ast::AbstractNode* node) {

  if (node->getKind() == triton::ast::BVXOR_NODE) {
    if (*(node->getChilds()[0]) == *(node->getChilds()[1]))
      return triton::ast::bv(0, node->getBitvectorSize());
  }

  return node;
}

int main(int ac, const char *av[]) {
  ...
  // Record a simplification callback
  api.recordSimplificationCallback(xor_simplification);
  ...
}
~~~~~~~~~~~~~

Another example (this time in Python) which replaces a node with this rule \f$ ((A \land \lnot{B}) \lor (\lnot{A} \land B)) \rightarrow (A \oplus B) \f$.

~~~~~~~~~~~~~{.py}
# Rule: if ((a & ~b) | (~a & b)) -> (a ^ b)
def xor_bitwise(node):

    def getNot(node):
        a = node.getChilds()[0]
        b = node.getChilds()[1]
        if a.getKind() == AST_NODE.BVNOT and b.getKind() != AST_NODE.BVNOT:
            return a
        if b.getKind() == AST_NODE.BVNOT and a.getKind() != AST_NODE.BVNOT:
            return b
        return None

    def getNonNot(node):
        a = node.getChilds()[0]
        b = node.getChilds()[1]
        if a.getKind() != AST_NODE.BVNOT and b.getKind() == AST_NODE.BVNOT:
            return a
        if b.getKind() != AST_NODE.BVNOT and a.getKind() == AST_NODE.BVNOT:
            return b
        return None

    if node.getKind() == AST_NODE.BVOR:
        c1 = node.getChilds()[0]
        c2 = node.getChilds()[1]
        if c1.getKind() == AST_NODE.BVAND and c2.getKind() == AST_NODE.BVAND:
            c1_not    = getNot(c1)
            c2_not    = getNot(c2)
            c1_nonNot = getNonNot(c1)
            c2_nonNot = getNonNot(c2)
            if c1_not == ~c2_nonNot and c1_not == ~c2_nonNot:
                return c1_nonNot ^ c2_nonNot
    return node


if __name__ == "__main__":

    # Set arch to init engines
    setArchitecture(ARCH.X86_64)

    # Record simplifications
    recordSimplificationCallback(xor_bitwise)

    a = bv(1, 8)
    b = bv(2, 8)
    c = (~b & a) | (~a & b)
    print 'Expr: ', c
    c = simplify(c)
    print 'Simp: ', c
~~~~~~~~~~~~~

\subsection SMT_simplification_z3 Simplification via Z3
<hr>

As Triton is able to convert a Triton's AST to a Z3's AST and vice versa, you can benefit to the power of Z3 to simplify your expression, then, come back to a Triton's AST and apply your own rules.

~~~~~~~~~~~~~{.py}
>>> enableSymbolicZ3Simplification(True)

>>> var = newSymbolicVariable(8)
>>> a = variable(var)
>>> b = bv(0x38, 8)
>>> c = bv(0xde, 8)
>>> d = bv(0x4f, 8)
>>> e = a * ((b & c) | d)

>>> print e
(bvmul SymVar_0 (bvor (bvand (_ bv56 8) (_ bv222 8)) (_ bv79 8)))

>>> f = simplify(e)
>>> print f
(bvmul (_ bv95 8) SymVar_0)
~~~~~~~~~~~~~

Note that applying a SMT simplification doesn't means that your expression will be more readable by an humain. For example, if we perform a simplification of a bitwise operation (as described in the
previous section), the new expression is not really useful for an humain.

~~~~~~~~~~~~~{.py}
>>> a = variable(var)
>>> b = bv(2, 8)
>>> c = (~b & a) | (~a & b) # a ^ b

>>> print c
(bvor (bvand (bvnot (_ bv2 8)) SymVar_0) (bvand (bvnot SymVar_0) (_ bv2 8)))

>>> d = simplify(c)
>>> print d
(concat ((_ extract 7 2) SymVar_0) (bvnot ((_ extract 1 1) SymVar_0)) ((_ extract 0 0) SymVar_0))
~~~~~~~~~~~~~

As you can see, Z3 tries to apply a bit-to-bit simplification. That's why, Triton allows you to deal with both, Z3's simplification passes and your own rules.

*/




namespace triton {
  namespace engines {
    namespace symbolic {


      SymbolicSimplification::SymbolicSimplification() {
        this->z3Enabled = false;
      }


      SymbolicSimplification::~SymbolicSimplification() {
      }


      bool SymbolicSimplification::isZ3SimplificationEnabled(void) const {
        return this->z3Enabled;
      }


      void SymbolicSimplification::enableZ3Simplification(bool flag) {
        this->z3Enabled = flag;
      }


      void SymbolicSimplification::recordSimplificationCallback(triton::engines::symbolic::sfp cb) {
        this->simplificationCallbacks.push_back(cb);
      }


      #ifdef TRITON_PYTHON_BINDINGS
      void SymbolicSimplification::recordSimplificationCallback(PyObject* cb) {
        if (!PyCallable_Check(cb))
          throw std::runtime_error("SymbolicSimplification::recordSimplificationCallback(): Expects a function callback as argument.");
        this->pySimplificationCallbacks.push_back(cb);
      }
      #endif


      void SymbolicSimplification::removeSimplificationCallback(triton::engines::symbolic::sfp cb) {
        this->simplificationCallbacks.remove(cb);
      }


      #ifdef TRITON_PYTHON_BINDINGS
      void SymbolicSimplification::removeSimplificationCallback(PyObject* cb) {
        this->pySimplificationCallbacks.remove(cb);
      }
      #endif


      triton::ast::AbstractNode* SymbolicSimplification::processSimplification(triton::ast::AbstractNode* node, bool z3) const {

        if (node == nullptr)
          throw std::runtime_error("SymbolicSimplification::processSimplification(): node cannot be null.");

        /* Check if we can use z3 to simplify the expression before using our own rules */
        if (this->z3Enabled | z3) {
          triton::ast::TritonToZ3Ast  z3Ast{false};
          triton::ast::Z3ToTritonAst  tritonAst{};
          triton::ast::Z3Result       result = z3Ast.eval(*node);

          /* Simplify and convert back to Triton's AST */
          z3::expr expr = result.getExpr().simplify();
          tritonAst.setExpr(expr);
          node = tritonAst.convert();
        }

        std::list<triton::engines::symbolic::sfp>::const_iterator it1;
        for (it1 = this->simplificationCallbacks.begin(); it1 != this->simplificationCallbacks.end(); it1++) {
          node = (*it1)(node);
          if (node == nullptr)
            throw std::runtime_error("SymbolicSimplification::processSimplification(): You cannot return a nullptr node.");
        }

        #ifdef TRITON_PYTHON_BINDINGS
        std::list<PyObject*>::const_iterator it2;
        for (it2 = this->pySimplificationCallbacks.begin(); it2 != this->pySimplificationCallbacks.end(); it2++) {

          /* Create function args */
          PyObject* args = triton::bindings::python::xPyTuple_New(1);
          PyTuple_SetItem(args, 0, triton::bindings::python::PyAstNode(node));

          /* Call the callback */
          PyObject* ret = PyObject_CallObject(*it2, args);

          /* Check the call */
          if (ret == nullptr) {
            PyErr_Print();
            throw std::runtime_error("SymbolicSimplification::processSimplification(): Fail to call the python callback.");
          }

          /* Check if the callback has returned a AbstractNode */
          if (!PyAstNode_Check(ret))
            throw std::runtime_error("SymbolicSimplification::processSimplification(): You must return a AstNode object.");

          /* Update node */
          node = PyAstNode_AsAstNode(ret);
          Py_DECREF(args);
        }
        #endif

        return node;
      }


    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

