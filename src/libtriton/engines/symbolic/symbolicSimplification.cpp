//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <list>
#include <map>

#include <triton/archEnums.hpp>
#include <triton/context.hpp>
#include <triton/exceptions.hpp>
#include <triton/modesEnums.hpp>
#include <triton/symbolicExpression.hpp>
#include <triton/symbolicSimplification.hpp>



/*! \page SMT_simplification_page SMT simplification passes
    \brief [**internal**] All information about the SMT simplification passes.

\tableofcontents
\section SMT_simplification_description Description
<hr>

Triton allows you to optimize your AST (See: \ref py_AstContext_page) just before the assignment to a register, a memory
or a volatile symbolic expression. The record of a simplification pass is really straightforward. You have to record your simplification
callback using the triton::Context::addCallback() function. Your simplification callback must takes as parameters a triton::Context and a
triton::ast::SharedAbstractNode. The callback must return a triton::ast::SharedAbstractNode. Then, your callback will be called before
every symbolic assignment. Note that you can record several simplification callbacks or remove a specific callback using the
triton::Context::removeCallback() function.

\subsection SMT_simplification_triton Simplification via Triton's rules
<hr>

Below, a little example which replaces all \f$ A \oplus A \rightarrow A = 0\f$.

~~~~~~~~~~~~~{.cpp}
// Rule: if (bvxor x x) -> (_ bv0 x_size)
triton::ast::SharedAbstractNode xor_simplification(triton::Context& ctx, const triton::ast::SharedAbstractNode& node) {

  if (node->getType() == triton::ast::BVXOR_NODE) {
    if (node->getChildren()[0]->equalTo(node->getChildren()[1]))
      return ctx.getAstContext().bv(0, node->getBitvectorSize());
  }

  return node;
}

int main(int ac, const char *av[]) {
  ...
  // Record a simplification callback
  ctx.addCallback(xor_simplification);
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
    ctx.addCallback(SYMBOLIC_SIMPLIFICATION, xor_bitwise)

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


      SymbolicSimplification::SymbolicSimplification(triton::arch::Architecture* architecture, triton::callbacks::Callbacks* callbacks) {
        this->architecture = architecture;
        this->callbacks = callbacks;
      }


      SymbolicSimplification::SymbolicSimplification(const SymbolicSimplification& other) {
        this->copy(other);
      }


      void SymbolicSimplification::copy(const SymbolicSimplification& other) {
        this->architecture = other.architecture;
        this->callbacks = other.callbacks;
      }


      triton::ast::SharedAbstractNode SymbolicSimplification::simplify(const triton::ast::SharedAbstractNode& node) const {
        std::list<triton::ast::SharedAbstractNode> worklist;
        triton::ast::SharedAbstractNode snode = node;

        if (node == nullptr)
          throw triton::exceptions::SymbolicSimplification("SymbolicSimplification::simplify(): node cannot be null.");

        if (this->callbacks && this->callbacks->isDefined(triton::callbacks::SYMBOLIC_SIMPLIFICATION)) {
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
            if (needs_update) {
              ast->init(true);
            }
          }
        }

        return snode;
      }


      triton::arch::BasicBlock SymbolicSimplification::simplify(const triton::arch::BasicBlock& block, bool padding) const {
        return this->deadStoreElimination(block, padding);
      }


      triton::arch::BasicBlock SymbolicSimplification::deadStoreElimination(const triton::arch::BasicBlock& block, bool padding) const {
        std::unordered_map<triton::usize, SharedSymbolicExpression> lifetime;
        std::map<triton::uint64, triton::arch::Instruction> instructions;
        triton::arch::BasicBlock out;
        triton::arch::BasicBlock in = block;

        if (block.getSize() == 0)
          return {};

        /* Define a temporary Context */
        triton::Context tmpctx(this->architecture->getArchitecture());

        /* Synch the concrete state */
        tmpctx.setConcreteState(*this->architecture);

        /* Execute the block */
        tmpctx.processing(in);

        /* Get all symbolic registers that were written */
        for (auto& reg : tmpctx.getSymbolicRegisters()) {
          for (auto& item : tmpctx.sliceExpressions(reg.second)) {
            lifetime[item.first] = item.second;
          }
        }

        /* Get all symbolic memory cells that were written */
        for (auto& mem : tmpctx.getSymbolicMemory()) {
          for (auto& item : tmpctx.sliceExpressions(mem.second)) {
            lifetime[item.first] = item.second;
          }
        }

        /* Keep instructions that build effective addresses (see #1174) */
        for (auto& inst : in.getInstructions()) {
          std::set<std::pair<triton::arch::MemoryAccess, triton::ast::SharedAbstractNode>> access;
          if (inst.isMemoryWrite()) {
            access = inst.getStoreAccess();
          }
          if (inst.isMemoryRead()) {
            access.insert(inst.getLoadAccess().begin(), inst.getLoadAccess().end());
          }
          for (const auto& x : access) {
            auto refs = triton::ast::search(x.second, triton::ast::REFERENCE_NODE);
            for (const auto& ref : refs) {
              auto expr = reinterpret_cast<triton::ast::ReferenceNode*>(ref.get())->getSymbolicExpression();
              auto eid = expr->getId();
              lifetime[eid] = expr;
            }
            if (x.first.getLeaAst()) {
              auto refs = triton::ast::search(x.first.getLeaAst(), triton::ast::REFERENCE_NODE);
              for (const auto& ref : refs) {
                auto expr = reinterpret_cast<triton::ast::ReferenceNode*>(ref.get())->getSymbolicExpression();
                auto eid = expr->getId();
                lifetime[eid] = expr;
              }
            }
          }
        }

        /* Get back the origin assembly of expressions that still alive */
        for (auto& se : lifetime) {
          if (se.second->getDisassembly().empty()) {
            continue;
          }
          auto addr = se.second->getAddress();
          for (auto& inst : in.getInstructions()) {
            if (inst.getAddress() == addr) {
              instructions[addr] = inst;
              break;
            }
          }
        }

        /* Create a new block with sorted instructions */
        auto lastaddr = in.getFirstAddress();
        auto nop = tmpctx.getNopInstruction();
        for (auto& item : instructions) {
          if (padding) {
            while (item.second.getAddress() > lastaddr) {
              out.add(nop);
              lastaddr += nop.getSize();
            }
          }
          out.add(item.second);
          lastaddr = item.second.getNextAddress();
        }

        return out;
      }


      SymbolicSimplification& SymbolicSimplification::operator=(const SymbolicSimplification& other) {
        this->copy(other);
        return *this;
      }

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */
