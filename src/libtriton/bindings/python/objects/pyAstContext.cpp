//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/astContext.hpp>
#include <triton/exceptions.hpp>
#include <triton/register.hpp>



/* setup doctest context

>>> from triton import REG, TritonContext, ARCH, Instruction, AST_REPRESENTATION
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)

>>> opcode = "\x48\x31\xD0"
>>> inst = Instruction()

>>> inst.setOpcode(opcode)
>>> inst.setAddress(0x400000)
>>> ctxt.setConcreteRegisterValue(ctxt.registers.rax, 12345)
>>> ctxt.setConcreteRegisterValue(ctxt.registers.rdx, 67890)

>>> ctxt.processing(inst)
True
>>> print inst
0x400000: xor rax, rdx

*/

/*! \page py_AstContext_page AstContext
    \brief [**python api**] All information about the ast python module.

\tableofcontents

\section ast_description Description
<hr>

Triton converts the x86 and the x86-64 instruction set semantics into AST representations which allows
you to perform precise analysis and allows you to build and to modify your own symbolic expressions.

\subsection ast_form_page AST Form
<hr>

~~~~~~~~~~~~~{.asm}
Instruction:  add rax, rdx
Expression:   ref!41 = (bvadd ((_ extract 63 0) ref!40) ((_ extract 63 0) ref!39))
~~~~~~~~~~~~~

As all Triton's expressions are on [SSA form](http://en.wikipedia.org/wiki/Static_single_assignment_form), the `ref!41` is the new expression of the `RAX`
register, the `ref!40` is the previous expression of the `RAX` register and the `ref!39` is the previous expression of the `RDX` register.
An \ref py_Instruction_page may contain several expressions (\ref py_SymbolicExpression_page). For example, the previous `add rax, rdx` instruction contains
7 expressions: 1 `ADD` semantics and 6 flags (`AF, CF, OF, PF, SF and ZF`) semantics where each flag is stored in a new \ref py_SymbolicExpression_page.

~~~~~~~~~~~~~{.asm}
Instruction: add rax, rdx
Expressions: ref!41 = (bvadd ((_ extract 63 0) ref!40) ((_ extract 63 0) ref!39))
             ref!42 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor ref!41 (bvxor ((_ extract 63 0) ref!40) ((_ extract 63 0) ref!39))))) (_ bv1 1) (_ bv0 1))
             ref!43 = (ite (bvult ref!41 ((_ extract 63 0) ref!40)) (_ bv1 1) (_ bv0 1))
             ref!44 = (ite (= ((_ extract 63 63) (bvand (bvxor ((_ extract 63 0) ref!40) (bvnot ((_ extract 63 0) ref!39))) (bvxor ((_ extract 63 0) ref!40) ref!41))) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
             ref!45 = (ite (= (parity_flag ((_ extract 7 0) ref!41)) (_ bv0 1)) (_ bv1 1) (_ bv0 1))
             ref!46 = (ite (= ((_ extract 63 63) ref!41) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
             ref!47 = (ite (= ref!41 (_ bv0 64)) (_ bv1 1) (_ bv0 1))
~~~~~~~~~~~~~

Triton deals with 64-bits registers (and 128-bits for SSE). It means that it uses the `concat` and `extract` functions when operations are performed on subregister.

~~~~~~~~~~~~~{.asm}
mov al, 0xff  -> ref!193 = (concat ((_ extract 63 8) ref!191) (_ bv255 8))
movsx eax, al -> ref!195 = ((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) ref!193)))
~~~~~~~~~~~~~

On the line 1, a new 64bit-vector is created with the concatenation of `RAX[63..8]` and the concretization of the value `0xff`. On the line 2, according
to the AMD64 behavior, if a 32-bit register is written, the CPU clears the 32-bit MSB of the corresponding register. So, in this case, we apply a sign
extension from al to `EAX`, then a zero extension from `EAX` to `RAX`.

\section ast_representation_page AST representation
<hr>

An abstract syntax tree ([AST](https://en.wikipedia.org/wiki/Abstract_syntax_tree)) is a representation of a grammar as tree. Triton uses a custom AST
for its expressions. As all expressions are built at runtime, an AST is available at each program point. For example, let assume this set of instructions:

~~~~~~~~~~~~~{.asm}
mov al, 1
mov cl, 10
mov dl, 20
xor cl, dl
add al, cl
~~~~~~~~~~~~~

At the line 5, the AST of the `AL` register looks like this:

<p align="center"><img width="400" src="https://triton.quarkslab.com/files/smt_ast.svg"/></p>

This AST represents the semantics of the `AL` register at the program point 5 from the program point 1. Note that this AST has been simplified for
a better comprehension. The real AST contains some `concat` and `extract` as mentioned in the previous chapter. According to the API you can build
and modify your own AST. Then, you can perform some modifications and simplifications before sending it to the solver.


\subsection ast_reference_node_page The AST reference node
<hr>

To manage more easily the subtree and to keep the SSA form of registers and memory, we have added a `REFERENCE` node which is a "terminate" node of a
tree but contains a reference to another subtree. Below, an example of one "partial" tree linked with two other subtrees.

<p align="center"><img width="600" src="https://triton.quarkslab.com/files/smt_ast_ref.svg"/></p>

If you try to go through the full AST you will fail at the first reference node because a reference node does not contains child nodes.
The only way to jump from a reference node to the targeted node is to use the triton::engines::symbolic::SymbolicEngine::getFullAst() function.

~~~~~~~~~~~~~{.py}
>>> zfId = ctxt.getSymbolicRegisterId(ctxt.registers.zf)
>>> partialTree = ctxt.getSymbolicExpressionFromId(zfId).getAst()
>>> print partialTree
(ite (= ref!0 (_ bv0 64)) (_ bv1 1) (_ bv0 1))

>>> fullTree = ctxt.getFullAst(partialTree)
>>> print fullTree
(ite (= (bvxor (_ bv12345 64) (_ bv67890 64)) (_ bv0 64)) (_ bv1 1) (_ bv0 1))

~~~~~~~~~~~~~

\subsection ast_smt_python_page The SMT or Python Syntax
<hr>

By default, Triton represents semantics into [SMT-LIB](http://smtlib.cs.uiowa.edu/) which is an international initiative aimed at facilitating research and development in Satisfiability Modulo Theories (SMT). However,
Triton allows you to display your AST via a Python syntax.

~~~~~~~~~~~~~{.py}
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)
>>> ctxt.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
>>> inst = Instruction()
>>> inst.setOpcode("\x48\x01\xd8") # add rax, rbx
>>> inst.setAddress(0x400000)
>>> ctxt.setConcreteRegisterValue(ctxt.registers.rax, 0x1122334455667788)
>>> ctxt.setConcreteRegisterValue(ctxt.registers.rbx, 0x8877665544332211)
>>> ctxt.processing(inst)
True
>>> print inst
0x400000: add rax, rbx

>>> for expr in inst.getSymbolicExpressions():
...     print expr
...
ref_0 = ((0x1122334455667788 + 0x8877665544332211) & 0xFFFFFFFFFFFFFFFF) # ADD operation
ref_1 = (0x1 if (0x10 == (0x10 & (ref_0 ^ (0x1122334455667788 ^ 0x8877665544332211)))) else 0x0) # Adjust flag
ref_2 = ((((0x1122334455667788 & 0x8877665544332211) ^ (((0x1122334455667788 ^ 0x8877665544332211) ^ ref_0) & (0x1122334455667788 ^ 0x8877665544332211))) >> 63) & 0x1) # Carry flag
ref_3 = ((((0x1122334455667788 ^ (~(0x8877665544332211) & 0xFFFFFFFFFFFFFFFF)) & (0x1122334455667788 ^ ref_0)) >> 63) & 0x1) # Overflow flag
ref_4 = ((((((((0x1 ^ (((ref_0 & 0xFF) >> 0x0) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x1) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x2) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x3) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x4) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x5) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x6) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x7) & 0x1)) # Parity flag
ref_5 = ((ref_0 >> 63) & 0x1) # Sign flag
ref_6 = (0x1 if (ref_0 == 0x0) else 0x0) # Zero flag
ref_7 = 0x400003 # Program Counter

# TODO : astRepresentation should not be a global value.
>>> ctxt.setAstRepresentationMode(AST_REPRESENTATION.SMT)

~~~~~~~~~~~~~

\section ast_py_examples_page Examples
<hr>

\subsection ast_py_examples_page_1 Get a register expression and ask for a model

~~~~~~~~~~~~~{.py}
>>> # Get the symbolic expression of the ZF flag
>>> zfId    = ctxt.getSymbolicRegisterId(ctxt.registers.zf)
>>> zfExpr  = ctxt.getFullAst(ctxt.getSymbolicExpressionFromId(zfId).getAst())

>>> astCtxt = ctxt.getAstContext()

>>> # (= zf True)
>>> newExpr = astCtxt.equal(
...             zfExpr,
...             astCtxt.bvtrue()
...           )

>>> # Get a model
>>> models = ctxt.getModel(newExpr)

~~~~~~~~~~~~~

\subsection ast_py_examples_page_2 Play with the AST

~~~~~~~~~~~~~{.py}
# Node information

>>> node = astCtxt.bvadd(astCtxt.bv(1, 8), astCtxt.bvxor(astCtxt.bv(10, 8), astCtxt.bv(20, 8)))
>>> print type(node)
<type 'AstNode'>

>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

>>> subchild = node.getChildren()[1].getChildren()[0]
>>> print subchild
(_ bv10 8)

>>> print subchild.getChildren()[0].getValue()
10
>>> print subchild.getChildren()[1].getValue()
8

# Node modification

>>> node = astCtxt.bvadd(astCtxt.bv(1, 8), astCtxt.bvxor(astCtxt.bv(10, 8), astCtxt.bv(20, 8)))
>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

>>> node.setChild(0, astCtxt.bv(123, 8))
True
>>> print node
(bvadd (_ bv123 8) (bvxor (_ bv10 8) (_ bv20 8)))

~~~~~~~~~~~~~

\subsection ast_py_examples_page_3 Python operators

~~~~~~~~~~~~~{.py}
>>> a = astCtxt.bv(1, 8)
>>> b = astCtxt.bv(2, 8)
>>> c = (a & ~b) | (~a & b)
>>> print c
(bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))

~~~~~~~~~~~~~

As we can't overload all AST's operators only these following operators are overloaded:

Python's Operator | e.g: SMT2-Lib format
------------------|------------------
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

\anchor ast
\section AstContext_py_api Python API - Methods of the AstContext module
<hr>

- <b>\ref py_AstNode_page bv(integer value, integer size)</b><br>
Creates a `bv` node (bitvector). The `size` must be in bits.<br>
e.g: `(_ bv<balue> size)`.

- <b>\ref py_AstNode_page bvadd(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvadd` node.<br>
e.g: `(bvadd expr1 epxr2)`.

- <b>\ref py_AstNode_page bvand(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvand` node.<br>
e.g: `(bvand expr1 epxr2)`.

- <b>\ref py_AstNode_page bvashr(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvashr` node.<br>
e.g: `(bvashr expr1 epxr2)`.

- <b>\ref py_AstNode_page bvfalse(void)</b><br>
This is an alias on the `(_ bv0 1)` ast expression.

- <b>\ref py_AstNode_page bvlshr(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvlshr` node.<br>
e.g: `(lshr expr1 epxr2)`.

- <b>\ref py_AstNode_page bvmul(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvmul` node.<br>
e.g: `(bvmul expr1 expr2)`.

- <b>\ref py_AstNode_page bvnand(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvnand` node.<br>
e.g: `(bvnand expr1 expr2)`.

- <b>\ref py_AstNode_page bvneg(\ref py_AstNode_page expr1)</b><br>
Creates a `bvneg` node.<br>
e.g: `(bvneg expr1)`.

- <b>\ref py_AstNode_page bvnor(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvnor` node.<br>
e.g: `(bvnor expr1 expr2)`.

- <b>\ref py_AstNode_page bvnot(\ref py_AstNode_page expr1)</b><br>
Creates a `bvnot` node.<br>
e.g: `(bvnot expr1)`.

- <b>\ref py_AstNode_page bvor(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvor` node.<br>
e.g: `(bvor expr1 expr2)`.

- <b>\ref py_AstNode_page bvror(integer displacement, \ref py_AstNode_page expr2)</b><br>
Creates a `bvror` node.<br>
e.g: `((_ rotate_right displacement) expr)`.

- <b>\ref py_AstNode_page bvrol(integer displacement, \ref py_AstNode_page expr2)</b><br>
Creates a `bvrol` node.<br>
e.g: `((_ rotate_left displacement) expr)`.

- <b>\ref py_AstNode_page bvsdiv(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsdiv` node.<br>
e.g: `(bvsdiv expr1 epxr2)`.

- <b>\ref py_AstNode_page bvsge(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsge` node.<br>
e.g: `(bvsge expr1 epxr2)`.

- <b>\ref py_AstNode_page bvsgt(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsgt` node.<br>
e.g: `(bvsgt expr1 epxr2)`.

- <b>\ref py_AstNode_page bvshl(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a Bvshl node.<br>
e.g: `(bvshl expr1 expr2)`.

- <b>\ref py_AstNode_page bvsle(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsle` node.<br>
e.g: `(bvsle expr1 epxr2)`.

- <b>\ref py_AstNode_page bvslt(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvslt` node.<br>
e.g: `(bvslt expr1 epxr2)`.

- <b>\ref py_AstNode_page bvsmod(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsmod` node.<br>
e.g: `(bvsmod expr1 expr2)`.

- <b>\ref py_AstNode_page bvsrem(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsrem` node.<br>
e.g: `(bvsrem expr1 expr2)`.

- <b>\ref py_AstNode_page bvsub(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsub` node.<br>
e.g: `(bvsub expr1 epxr2)`.

- <b>\ref py_AstNode_page bvtrue(void)</b><br>
This is an alias on the `(_ bv1 1)` ast expression.<br>

- <b>\ref py_AstNode_page bvudiv(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvudiv` node.<br>
e.g: `(bvudiv expr1 epxr2)`.

- <b>\ref py_AstNode_page bvuge(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvuge` node.<br>
e.g: `(bvuge expr1 epxr2)`.

- <b>\ref py_AstNode_page bvugt(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvugt` node.<br>
e.g: `(bvugt expr1 epxr2)`.

- <b>\ref py_AstNode_page bvule(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvule` node.<br>
e.g: `(bvule expr1 epxr2)`.

- <b>\ref py_AstNode_page bvult(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvult` node.<br>
e.g: `(bvult expr1 epxr2)`.

- <b>\ref py_AstNode_page bvurem(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvurem` node.<br>
e.g: `(bvurem expr1 expr2)`.

- <b>\ref py_AstNode_page bvxnor(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvxnor` node.<br>
e.g: `(bvxnor expr1 expr2)`.

- <b>\ref py_AstNode_page bvxor(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvxor` node.<br>
e.g: `(bvxor expr1 epxr2)`.

- <b>\ref py_AstNode_page concat([\ref py_AstNode_page expr ...])</b><br>
Concatenates several nodes.

- <b>\ref py_AstNode_page distinct(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `distinct` node.<br>
e.g: `(distinct expr1 expr2)`

- <b>\ref py_AstNode_page duplicate(\ref py_AstNode_page expr)</b><br>
Duplicates the node and returns a new instance as \ref py_AstNode_page. When you play with a node, it's recommended to use this function before any manipulation.

- <b>\ref py_AstNode_page equal(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates an `equal` node.<br>
e.g: `(= expr1 epxr2)`.

- <b>\ref py_AstNode_page extract(integer high, integer low, \ref py_AstNode_page expr1)</b><br>
Creates an `extract` node. The `high` and `low` fields represent the bits position.<br>
e.g: `((_ extract high low) expr1)`.

- <b>\ref py_AstNode_page ite(\ref py_AstNode_page ifExpr, \ref py_AstNode_page thenExpr, \ref py_AstNode_page elseExpr)</b><br>
Creates an `ite` node.<br>
e.g: `(ite ifExpr thenExpr elseExpr)`.

- <b>\ref py_AstNode_page land([\ref py_AstNode_page expr ...])</b><br>
Creates a logical `AND` on several nodes.
e.g: `(and expr1 expr2 expr3 expr4)`.

- <b>\ref py_AstNode_page let(string alias, \ref py_AstNode_page expr2, \ref py_AstNode_page expr3)</b><br>
Creates a `let` node.<br>
e.g: `(let ((alias expr2)) expr3)`.

- <b>\ref py_AstNode_page lnot(\ref py_AstNode_page expr)</b><br>
Creates a `lnot` node (logical NOT).<br>
e.g: `(not expr)`.

- <b>\ref py_AstNode_page lor([\ref py_AstNode_page expr ...])</b><br>
Creates a logical `OR` on several nodes.
e.g: `(or expr1 expr2 expr3 expr4)`.

- <b>\ref py_AstNode_page reference(integer exprId)</b><br>
Creates a reference node (SSA-based).<br>
e.g: `ref!123`.

- <b>\ref py_AstNode_page string(string s)</b><br>
Creates a `string` node.

- <b>\ref py_AstNode_page sx(integer sizeExt, \ref py_AstNode_page expr1)</b><br>
Creates a `sx` node (sign extend).<br>
e.g: `((_ sign_extend sizeExt) expr1)`.

- <b>\ref py_AstNode_page variable(\ref py_SymbolicVariable_page symVar)</b><br>
Creates a `variable` node.

- <b>\ref py_AstNode_page zx(integer sizeExt, \ref py_AstNode_page expr1)</b><br>
Creates a `zx` node (zero extend).<br>
e.g: `((_ zero_extend sizeExt) expr1)`.

*/


namespace triton {
  namespace bindings {
    namespace python {


      static PyObject* AstContext_bv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as first argument");

        if (op2 == nullptr || (!PyLong_Check(op2) && !PyInt_Check(op2)))
          return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bv(PyLong_AsUint512(op1), PyLong_AsUint32(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvadd(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvadd(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvadd(): expected a AstNode as second argument");

        try {
          // FIXME: Should we check all astContext are sames
          return PyAstNode(PyAstContext_AsAstContext(self)->bvadd(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvand(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvand(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvand(): expected a AstNode as second argument");

        try {
          // FIXME: Should we check all astContext are sames
          return PyAstNode(PyAstContext_AsAstContext(self)->bvand(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvashr(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvashr(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvashr(): expected a AstNode as second argument");

        try {
          // FIXME: Should we check all astContext are sames
          return PyAstNode(PyAstContext_AsAstContext(self)->bvashr(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvfalse(PyObject* self, PyObject* args) {
        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvfalse());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvtrue(PyObject* self, PyObject* args) {
        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvtrue());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvlshr(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvlshr(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvmul(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvmul(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvmul(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvmul(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvnand(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnand(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvnand(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvnand(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvneg(PyObject* self, PyObject* op1) {
        if (!PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvneg(): expected a AstNode as first argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvneg(PyAstNode_AsAstNode(op1)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvnor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvnor(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvnor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvnot(PyObject* self, PyObject* op1) {
        if (!PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnot(): expected a AstNode as first argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvnot(PyAstNode_AsAstNode(op1)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvor(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvror(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected an integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvror(PyLong_AsUint32(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvrol(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvrol(PyLong_AsUint32(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsdiv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsdiv(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsge(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsge(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsge(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsge(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsgt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsgt(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvshl(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvshl(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvshl(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvshl(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsle(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsle(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsle(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsle(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvslt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvslt(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvslt(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvslt(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsmod(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsmod(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsrem(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsrem(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvsub(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsub(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsub(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvsub(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvudiv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvudiv(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvuge(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvuge(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvuge(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvuge(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvugt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvugt(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvugt(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvugt(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvule(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvule(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvule(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvule(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvult(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvult(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvult(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvult(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvurem(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvurem(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvurem(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvurem(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvxnor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvxnor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_bvxor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvxor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvxor(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvxor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_distinct(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "distinct(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "distinct(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->distinct(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_duplicate(PyObject* self, PyObject* expr) {
        if (!PyAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "duplicate(): expected a AstNode as argument");

        try {
          return PyAstNode(triton::ast::newInstance(PyAstNode_AsAstNode(expr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_concat(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::AbstractNode *> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "concat(): expected a list of AstNodes as first argument");

        /* Check if the list contains only PyAstNode */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PyAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "concat(): Each element from the list must be a AstNode");

          exprs.push_back(PyAstNode_AsAstNode(item));
        }

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->concat(exprs));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_equal(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "equal(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "equal(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->equal(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_extract(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        PyObject* op3 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2, &op3);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "extract(): expected an integer as first argument");

        if (op2 == nullptr || (!PyLong_Check(op2) && !PyInt_Check(op2)))
          return PyErr_Format(PyExc_TypeError, "extract(): expected an integer as second argument");

        if (op3 == nullptr || !PyAstNode_Check(op3))
          return PyErr_Format(PyExc_TypeError, "extract(): expected a AstNode as third argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->extract(PyLong_AsUint32(op1), PyLong_AsUint32(op2), PyAstNode_AsAstNode(op3)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_ite(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        PyObject* op3 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2, &op3);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "ite(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "ite(): expected a AstNode as second argument");

        if (op3 == nullptr || !PyAstNode_Check(op3))
          return PyErr_Format(PyExc_TypeError, "ite(): expected a AstNode as third argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->ite(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2), PyAstNode_AsAstNode(op3)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_land(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::AbstractNode *> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "land(): expected a list of AstNodes as first argument");

        /* Check if the list contains only PyAstNode */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PyAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "land(): Each element from the list must be a AstNode");

          exprs.push_back(PyAstNode_AsAstNode(item));
        }

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->land(exprs));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_let(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        PyObject* op3 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2, &op3);

        if (op1 == nullptr || !PyString_Check(op1))
          return PyErr_Format(PyExc_TypeError, "let(): expected a string as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "let(): expected a AstNode as second argument");

        if (op3 == nullptr || !PyAstNode_Check(op3))
          return PyErr_Format(PyExc_TypeError, "let(): expected a AstNode as third argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->let(PyString_AsString(op1), PyAstNode_AsAstNode(op2), PyAstNode_AsAstNode(op3)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_lnot(PyObject* self, PyObject* expr) {
        if (expr == nullptr || !PyAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "lnot(): expected a AstNode as argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->lnot(PyAstNode_AsAstNode(expr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_lor(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::AbstractNode *> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "lor(): expected a list of AstNodes as first argument");

        /* Check if the list contains only PyAstNode */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PyAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "lor(): Each element from the list must be a AstNode");

          exprs.push_back(PyAstNode_AsAstNode(item));
        }

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->lor(exprs));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_reference(PyObject* self, PyObject* symExpr) {
        if (!PySymbolicExpression_Check(symExpr))
          return PyErr_Format(PyExc_TypeError, "reference(): expected a symbolic expression as argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->reference(*PySymbolicExpression_AsSymbolicExpression(symExpr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_string(PyObject* self, PyObject* expr) {
        if (!PyString_Check(expr))
          return PyErr_Format(PyExc_TypeError, "string(): expected a string as first argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->string(PyString_AsString(expr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_sx(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "sx(): expected an integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "sx(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->sx(PyLong_AsUint32(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_variable(PyObject* self, PyObject* symVar) {
        if (!PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "variable(): expected a SymbolicVariable as first argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->variable(*PySymbolicVariable_AsSymbolicVariable(symVar)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_zx(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "zx(): expected an integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "zx(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->zx(PyLong_AsUint32(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      //! AstContext methods.
      PyMethodDef AstContext_callbacks[] = {
        {"bv",            AstContext_bv,              METH_VARARGS,     ""},
        {"bvadd",         AstContext_bvadd,           METH_VARARGS,     ""},
        {"bvand",         AstContext_bvand,           METH_VARARGS,     ""},
        {"bvashr",        AstContext_bvashr,          METH_VARARGS,     ""},
        {"bvfalse",       AstContext_bvfalse,         METH_NOARGS,      ""},
        {"bvtrue",        AstContext_bvtrue,          METH_NOARGS,      ""},
        {"bvlshr",        AstContext_bvlshr,          METH_VARARGS,     ""},
        {"bvmul",         AstContext_bvmul,           METH_VARARGS,     ""},
        {"bvnand",        AstContext_bvnand,          METH_VARARGS,     ""},
        {"bvneg",         AstContext_bvneg,           METH_O,           ""},
        {"bvnor",         AstContext_bvnor,           METH_VARARGS,     ""},
        {"bvnot",         AstContext_bvnot,           METH_O,           ""},
        {"bvor",          AstContext_bvor,            METH_VARARGS,     ""},
        {"bvrol",         AstContext_bvrol,           METH_VARARGS,     ""},
        {"bvror",         AstContext_bvror,           METH_VARARGS,     ""},
        {"bvsdiv",        AstContext_bvsdiv,          METH_VARARGS,     ""},
        {"bvsge",         AstContext_bvsge,           METH_VARARGS,     ""},
        {"bvsgt",         AstContext_bvsgt,           METH_VARARGS,     ""},
        {"bvshl",         AstContext_bvshl,           METH_VARARGS,     ""},
        {"bvsle",         AstContext_bvsle,           METH_VARARGS,     ""},
        {"bvslt",         AstContext_bvslt,           METH_VARARGS,     ""},
        {"bvsmod",        AstContext_bvsmod,          METH_VARARGS,     ""},
        {"bvsrem",        AstContext_bvsrem,          METH_VARARGS,     ""},
        {"bvsub",         AstContext_bvsub,           METH_VARARGS,     ""},
        {"bvudiv",        AstContext_bvudiv,          METH_VARARGS,     ""},
        {"bvuge",         AstContext_bvuge,           METH_VARARGS,     ""},
        {"bvugt",         AstContext_bvugt,           METH_VARARGS,     ""},
        {"bvule",         AstContext_bvule,           METH_VARARGS,     ""},
        {"bvult",         AstContext_bvult,           METH_VARARGS,     ""},
        {"bvurem",        AstContext_bvurem,          METH_VARARGS,     ""},
        {"bvxnor",        AstContext_bvxnor ,         METH_VARARGS,     ""},
        {"bvxor",         AstContext_bvxor,           METH_VARARGS,     ""},
        {"concat",        AstContext_concat,          METH_O,           ""},
        {"distinct",      AstContext_distinct,        METH_VARARGS,     ""},
        {"duplicate",     AstContext_duplicate,       METH_O,           ""},
        {"equal",         AstContext_equal,           METH_VARARGS,     ""},
        {"extract",       AstContext_extract,         METH_VARARGS,     ""},
        {"ite",           AstContext_ite,             METH_VARARGS,     ""},
        {"land",          AstContext_land,            METH_O,           ""},
        {"let",           AstContext_let,             METH_VARARGS,     ""},
        {"lnot",          AstContext_lnot,            METH_O,           ""},
        {"lor",           AstContext_lor,             METH_O,           ""},
        {"reference",     AstContext_reference,       METH_O,           ""},
        {"string",        AstContext_string,          METH_O,           ""},
        {"sx",            AstContext_sx,              METH_VARARGS,     ""},
        {"variable",      AstContext_variable,        METH_O,           ""},
        {"zx",            AstContext_zx,              METH_VARARGS,     ""},
        {nullptr,         nullptr,                    0,                nullptr}
      };


      //! Python description for an ast context.
      PyTypeObject AstContext_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "AstContext",                               /* tp_name */
        sizeof(AstContext_Object),                  /* tp_basicsize */
        0,                                          /* tp_itemsize */
        0,                                          /* tp_dealloc */
        0,                                          /* tp_print */
        0,                                          /* tp_getattr */
        0,                                          /* tp_setattr */
        0,                                          /* tp_compare */
        0,                                          /* tp_repr */
        0,                                          /* tp_as_number */
        0,                                          /* tp_as_sequence */
        0,                                          /* tp_as_mapping */
        0,                                          /* tp_hash */
        0,                                          /* tp_call */
        0,                                          /* tp_str */
        0,                                          /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "AstContext objects",                       /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        AstContext_callbacks,                       /* tp_methods */
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
        0,                                          /* tp_free */
        0,                                          /* tp_is_gc */
        0,                                          /* tp_bases */
        0,                                          /* tp_mro */
        0,                                          /* tp_cache */
        0,                                          /* tp_subclasses */
        0,                                          /* tp_weaklist */
        0,                                          /* tp_del */
        0                                           /* tp_version_tag */
      };


      PyObject* PyAstContext(triton::ast::AstContext& ctxt) {
        PyType_Ready(&AstContext_Type);
        AstContext_Object* object = PyObject_NEW(AstContext_Object, &AstContext_Type);

        if (object != nullptr)
          object->ctxt = &ctxt;

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
