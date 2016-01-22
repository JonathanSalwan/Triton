//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>
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

Triton allows you to optimize your AST of SMT just before the assignment to a register, a memory
or a volatile symbolic expression.

<p align="center"><img src="http://triton.quarkslab.com/files/simplification.png"/></p>

The record of a simplification pass is really straightforward. You have to record your simplification
callback using the triton::API::recordSimplificationCallback() function. Your simplification callback
must takes as unique parameter a pointer of triton::smt2lib::smtAstAbstractNode and returns a pointer of
triton::smt2lib::smtAstAbstractNode. Then, your callback will be called before every symbolic assignment.
Note that you can record several simplification callbacks or remove a specific callback using the
triton::API::removeSimplificationCallback() function.

Below, a little example which replaces all \f$ A \oplus A \rightarrow A = 0\f$.

~~~~~~~~~~~~~{.cpp}
// Rule: if (bvxor x x) -> (_ bv0 x_size)
smt2lib::smtAstAbstractNode* xor_simplification(smt2lib::smtAstAbstractNode* node) {

  if (node->getKind() == smt2lib::BVXOR_NODE) {
    if (*(node->getChilds()[0]) == *(node->getChilds()[1]))
      return smt2lib::bv(0, node->getBitvectorSize());
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
        if a.getKind() == SMT_AST_NODE.BVNOT and b.getKind() != SMT_AST_NODE.BVNOT:
            return a
        if b.getKind() == SMT_AST_NODE.BVNOT and a.getKind() != SMT_AST_NODE.BVNOT:
            return b
        return None

    def getNonNot(node):
        a = node.getChilds()[0]
        b = node.getChilds()[1]
        if a.getKind() != SMT_AST_NODE.BVNOT and b.getKind() == SMT_AST_NODE.BVNOT:
            return a
        if b.getKind() != SMT_AST_NODE.BVNOT and a.getKind() == SMT_AST_NODE.BVNOT:
            return b
        return None

    if node.getKind() == SMT_AST_NODE.BVOR:
        c1 = node.getChilds()[0]
        c2 = node.getChilds()[1]
        if c1.getKind() == SMT_AST_NODE.BVAND and c2.getKind() == SMT_AST_NODE.BVAND:
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

*/




namespace triton {
  namespace engines {
    namespace symbolic {


      SymbolicSimplification::SymbolicSimplification() {
      }


      SymbolicSimplification::~SymbolicSimplification() {
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


      smt2lib::smtAstAbstractNode* SymbolicSimplification::processSimplification(smt2lib::smtAstAbstractNode* node) {

        std::list<triton::engines::symbolic::sfp>::iterator it1;
        for (it1 = this->simplificationCallbacks.begin(); it1 != this->simplificationCallbacks.end(); it1++) {
          node = (*it1)(node);
          if (node == nullptr)
            throw std::runtime_error("SymbolicSimplification::processSimplification(): You cannot return a nullptr node.");
        }

        #ifdef TRITON_PYTHON_BINDINGS
        std::list<PyObject*>::iterator it2;
        for (it2 = this->pySimplificationCallbacks.begin(); it2 != this->pySimplificationCallbacks.end(); it2++) {

          /* Create function args */
          PyObject* args = triton::bindings::python::xPyTuple_New(1);
          PyTuple_SetItem(args, 0, triton::bindings::python::PySmtAstNode(node));

          /* Call the callback */
          PyObject* ret = PyObject_CallObject(*it2, args);

          /* Check the call */
          if (ret == nullptr) {
            PyErr_Print();
            throw std::runtime_error("SymbolicSimplification::processSimplification(): Fail to call the python callback.");
          }

          /* Check if the callback has returned a smtAstAbstractNode */
          if (!PySmtAstNode_Check(ret))
            throw std::runtime_error("SymbolicSimplification::processSimplification(): You must return a SmtAstNode object.");

          /* Update node */
          node = PySmtAstNode_AsSmtAstNode(ret);
          Py_DECREF(args);
        }
        #endif

        return node;
      }


    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

