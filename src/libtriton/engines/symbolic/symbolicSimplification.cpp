//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <list>
#include <triton/exceptions.hpp>
#include <triton/symbolicSimplification.hpp>



/*! \page SMT_simplification_page SMT simplification passes
    \brief [**internal**] All information about the SMT simplification passes.

\tableofcontents
\section SMT_simplification_description Description
<hr>

Triton allows you to optimize your AST (See: \ref py_AstContext_page) just before the assignment to a register, a memory
or a volatile symbolic expression. The record of a simplification pass is really straightforward. You have to record your simplification
callback using the triton::API::addCallback() function. Your simplification callback
must takes as parameters a triton::API and a triton::ast::SharedAbstractNode. The callback must return a triton::ast::SharedAbstractNode.
Then, your callback will be called before every symbolic assignment. Note that you can record several simplification callbacks or
remove a specific callback using the triton::API::removeCallback() function.

\subsection SMT_simplification_triton Simplification via Triton's rules
<hr>

Below, a little example which replaces all \f$ A \oplus A \rightarrow A = 0\f$.

~~~~~~~~~~~~~{.cpp}
// Rule: if (bvxor x x) -> (_ bv0 x_size)
triton::ast::SharedAbstractNode xor_simplification(triton::API& ctx, const triton::ast::SharedAbstractNode& node) {

  if (node->getType() == triton::ast::BVXOR_NODE) {
    if (node->getChildren()[0]->equalTo(node->getChildren()[1]))
      return ctx.getAstContext().bv(0, node->getBitvectorSize());
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
def xor_bitwise(ctx, node):

    def getNot(node):
        a = node.getChildren()[0]
        b = node.getChildren()[1]
        if a.getType() == AST_NODE.BVNOT and b.getType() != AST_NODE.BVNOT:
            return a
        if b.getType() == AST_NODE.BVNOT and a.getType() != AST_NODE.BVNOT:
            return b
        return None

    def getNonNot(node):
        a = node.getChildren()[0]
        b = node.getChildren()[1]
        if a.getType() != AST_NODE.BVNOT and b.getType() == AST_NODE.BVNOT:
            return a
        if b.getType() != AST_NODE.BVNOT and a.getType() == AST_NODE.BVNOT:
            return b
        return None

    if node.getType() == AST_NODE.BVOR:
        c1 = node.getChildren()[0]
        c2 = node.getChildren()[1]
        if c1.getType() == AST_NODE.BVAND and c2.getType() == AST_NODE.BVAND:
            c1_not    = getNot(c1)
            c2_not    = getNot(c2)
            c1_nonNot = getNonNot(c1)
            c2_nonNot = getNonNot(c2)
            if c1_not.equalTo(~c2_nonNot) and c2_not.equalTo(~c1_nonNot):
                return c1_nonNot ^ c2_nonNot
    return node


if __name__ == "__main__":
    ctx = TritonContext()

    # Set arch to init engines
    ctx.setArchitecture(ARCH.X86_64)

    # Record simplifications
    ctx.addCallback(xor_bitwise, SYMBOLIC_SIMPLIFICATION)

    a = bv(1, 8)
    b = bv(2, 8)
    c = (~b & a) | (~a & b)
    print 'Expr: ', c
    c = ctx.simplify(c)
    print 'Simp: ', c
~~~~~~~~~~~~~

\subsection SMT_simplification_z3 Simplification via Z3
<hr>

As Triton is able to convert a Triton's AST to a Z3's AST and vice versa, you can benefit to the power of Z3
to simplify your expression, then, come back to a Triton's AST and apply your own rules.

~~~~~~~~~~~~~{.py}
>>> var = ctx.newSymbolicVariable(8)
>>> a = ctx.getAstContext().variable(var)
>>> b = bv(0x38, 8)
>>> c = bv(0xde, 8)
>>> d = bv(0x4f, 8)
>>> e = a * ((b & c) | d)

>>> print e
(bvmul SymVar_0 (bvor (bvand (_ bv56 8) (_ bv222 8)) (_ bv79 8)))

>>> usingZ3 = True
>>> f = ctx.simplify(e, usingZ3)
>>> print f
(bvmul (_ bv95 8) SymVar_0)
~~~~~~~~~~~~~

Note that applying a SMT simplification doesn't means that your expression will be more readable by an humain.
For example, if we perform a simplification of a bitwise operation (as described in the previous section), the
new expression is not really useful for an humain.

~~~~~~~~~~~~~{.py}
>>> a = ctx.getAstContext().variable(var)
>>> b = bv(2, 8)
>>> c = (~b & a) | (~a & b) # a ^ b

>>> print c
(bvor (bvand (bvnot (_ bv2 8)) SymVar_0) (bvand (bvnot SymVar_0) (_ bv2 8)))

>>> d = ctx.simplify(c, True)
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


      SymbolicSimplification::SymbolicSimplification(const SymbolicSimplification& other) {
        this->copy(other);
      }


      void SymbolicSimplification::copy(const SymbolicSimplification& other) {
        this->callbacks = other.callbacks;
      }


      triton::ast::SharedAbstractNode SymbolicSimplification::processSimplification(const triton::ast::SharedAbstractNode& node) const {
        std::list<triton::ast::SharedAbstractNode> worklist;
        triton::ast::SharedAbstractNode snode = node;

        if (node == nullptr)
          throw triton::exceptions::SymbolicSimplification("SymbolicSimplification::processSimplification(): node cannot be null.");

        if (this->callbacks) {
          snode = this->callbacks->processCallbacks(triton::callbacks::SYMBOLIC_SIMPLIFICATION, node);
          /*
           *  We use a worklist strategy to avoid recursive calls
           *  and so stack overflow when going through a big AST.
           */
          worklist.push_back(snode);
          while (worklist.size()) {
            auto ast = worklist.front();
            worklist.pop_front();
            bool needs_update = false;
            for (triton::uint32 index = 0; index < ast->getChildren().size(); index++) {
              auto child = ast->getChildren()[index];
              /* Don't apply simplification on nodes like String, Integer, etc. */
              if (child->getBitvectorSize()) {
                auto schild = this->callbacks->processCallbacks(triton::callbacks::SYMBOLIC_SIMPLIFICATION, child);
                ast->setChild(index, schild);
                needs_update |= !schild->canReplaceNodeWithoutUpdate(child);
                worklist.push_back(schild);
              }
            }
            if (needs_update)
              ast->init();
          }
        }

        return snode;
      }


      SymbolicSimplification& SymbolicSimplification::operator=(const SymbolicSimplification& other) {
        this->copy(other);
        return *this;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
