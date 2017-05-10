//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/exceptions.hpp>
#include <triton/symbolicSimplification.hpp>



/*! \page SMT_simplification_page SMT simplification passes
    \brief [**internal**] All information about the SMT simplification passes.

\tableofcontents
\section SMT_simplification_description Description
<hr>

Triton allows you to optimize your AST (See: \ref py_ast_page) just before the assignment to a register, a memory
or a volatile symbolic expression.

<p align="center"><img src="https://triton.quarkslab.com/files/simplification.png"/></p>

The record of a simplification pass is really straightforward. You have to record your simplification
callback using the triton::API::addCallback() function. Your simplification callback
must takes as unique parameter a pointer of triton::ast::AbstractNode and returns a pointer of
triton::ast::AbstractNode. Then, your callback will be called before every symbolic assignment.
Note that you can record several simplification callbacks or remove a specific callback using the
triton::API::removeCallback() function.

\subsection SMT_simplification_triton Simplification via Triton's rules
<hr>

Below, a little example which replaces all \f$ A \oplus A \rightarrow A = 0\f$.

~~~~~~~~~~~~~{.cpp}
// Rule: if (bvxor x x) -> (_ bv0 x_size)
triton::ast::AbstractNode* xor_simplification(triton::ast::AbstractNode* node) {

  if (node->getKind() == triton::ast::BVXOR_NODE) {
    if (node->getChilds()[0]->equalTo(node->getChilds()[1]))
      return triton::ast::bv(0, node->getBitvectorSize());
  }

  return node;
}

int main(int ac, const char *av[]) {
  ...
  // Record a simplification callback
  api.addCallback(xor_simplification);
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
            if c1_not.equalTo(~c2_nonNot) and c2_not.equalTo(~c1_nonNot):
                return c1_nonNot ^ c2_nonNot
    return node


if __name__ == "__main__":

    # Set arch to init engines
    setArchitecture(ARCH.X86_64)

    # Record simplifications
    addCallback(xor_bitwise, SYMBOLIC_SIMPLIFICATION)

    a = bv(1, 8)
    b = bv(2, 8)
    c = (~b & a) | (~a & b)
    print 'Expr: ', c
    c = simplify(c)
    print 'Simp: ', c
~~~~~~~~~~~~~

\subsection SMT_simplification_z3 Simplification via Z3
<hr>

As Triton is able to convert a Triton's AST to a Z3's AST and vice versa, you can benefit to the power of Z3
to simplify your expression, then, come back to a Triton's AST and apply your own rules.

~~~~~~~~~~~~~{.py}
>>> var = newSymbolicVariable(8)
>>> a = variable(var)
>>> b = bv(0x38, 8)
>>> c = bv(0xde, 8)
>>> d = bv(0x4f, 8)
>>> e = a * ((b & c) | d)

>>> print e
(bvmul SymVar_0 (bvor (bvand (_ bv56 8) (_ bv222 8)) (_ bv79 8)))

>>> usingZ3 = True
>>> f = simplify(e, usingZ3)
>>> print f
(bvmul (_ bv95 8) SymVar_0)
~~~~~~~~~~~~~

Note that applying a SMT simplification doesn't means that your expression will be more readable by an humain.
For example, if we perform a simplification of a bitwise operation (as described in the previous section), the
new expression is not really useful for an humain.

~~~~~~~~~~~~~{.py}
>>> a = variable(var)
>>> b = bv(2, 8)
>>> c = (~b & a) | (~a & b) # a ^ b

>>> print c
(bvor (bvand (bvnot (_ bv2 8)) SymVar_0) (bvand (bvnot SymVar_0) (_ bv2 8)))

>>> d = simplify(c, True)
>>> print d
(concat ((_ extract 7 2) SymVar_0) (bvnot ((_ extract 1 1) SymVar_0)) ((_ extract 0 0) SymVar_0))
~~~~~~~~~~~~~

As you can see, Z3 tries to apply a bit-to-bit simplification. That's why, Triton allows you to deal with both,
Z3's simplification passes and your own rules.

*/




namespace triton {
  namespace engines {
    namespace symbolic {


      SymbolicSimplification::SymbolicSimplification(triton::callbacks::Callbacks* callbacks) {
        this->callbacks = callbacks;
      }


      SymbolicSimplification::SymbolicSimplification(const SymbolicSimplification& copy) {
        this->copy(copy);
      }


      SymbolicSimplification::~SymbolicSimplification() {
      }


      void SymbolicSimplification::copy(const SymbolicSimplification& other) {
        this->callbacks = other.callbacks;
      }


      triton::ast::AbstractNode* SymbolicSimplification::processSimplification(triton::ast::AbstractNode* node) const {
        if (node == nullptr)
          throw triton::exceptions::SymbolicSimplification("SymbolicSimplification::processSimplification(): node cannot be null.");

        /* process recorded callback about symbolic simplifications */
        if (this->callbacks)
          node = this->callbacks->processCallbacks(triton::callbacks::SYMBOLIC_SIMPLIFICATION, node);

        return node;
      }


      void SymbolicSimplification::operator=(const SymbolicSimplification& other) {
        this->copy(other);
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

