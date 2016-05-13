//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <ast.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>



/*! \page py_ast_page AST Representations
    \brief [**python api**] All information about the ast python module.
    \anchor ast

\tableofcontents

\section ast_description Description
<hr>

Triton converts the x86 and the x86-64 instruction set semantics into AST representations which allows you to perform precise analysis and allow you to build and to
modify your own symbolic expressions.

~~~~~~~~~~~~~{.py}
>>> from triton import ast
>>> ast
<module 'ast' (built-in)>
~~~~~~~~~~~~~

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

<p align="center"><img width="400" src="http://triton.quarkslab.com/files/smt_ast.svg"/></p>

This AST represents the semantics of the `AL` register at the program point 5 from the program point 1. Note that this AST has been simplified for
a better comprehension. The real AST contains some `concat` and `extract` as mentioned in the previous chapter. According to the API you can build
and modify your own AST. Then, you can perform some modifications and simplifications before sending it to the solver.


\subsection ast_reference_node_page The AST reference node
<hr>

To manage more easily the subtree and to keep the SSA form of registers and memory, we have added a `REFERENCE` node which is a "terminate" node of a
tree but contains a reference to another subtree. Below, an example of one "partial" tree linked with two other subtrees.

<p align="center"><img width="600" src="http://triton.quarkslab.com/files/smt_ast_ref.svg"/></p>

If you try to go through the full AST you will fail at the first reference node because a reference node does not contains child nodes.
The only way to jump from a reference node to the targeted node is to use the triton::engines::symbolic::SymbolicEngine::getFullAst() function.

~~~~~~~~~~~~~{.py}
>>> zfId = getSymbolicRegisterId(REG.ZF)
>>> partialTree = getSymbolicExpressionFromId(zfId).getAst()
>>> print partialTree
(ite (= ref!89 (_ bv0 32)) (_ bv1 1) (_ bv0 1))

>>> fullTree = getFullAst(partialTree)
>>> print fullTree
(ite (= (bvsub ((_ extract 31 0) ((_ zero_extend 32) ((_ extract 31 0) ((_ zero_extend 32) (bvxor ((_ extract 31 0) ((_ zero_extend 32) (bvsub ((_ extract 31 0) ((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) SymVar_0)))) (_ bv1 32)))) (_ bv85 32)))))) ((_ extract 31 0) ((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (_ bv49 8))))))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
~~~~~~~~~~~~~

\subsection ast_smt_python_page The SMT or Python Syntax
<hr>

By default, Triton represents semantics into [SMT-LIB](http://smtlib.cs.uiowa.edu/) which is an international initiative aimed at facilitating research and development in Satisfiability Modulo Theories (SMT). However,
Triton allows you to display your AST via a Python syntax.

~~~~~~~~~~~~~{.py}
>>> from triton import *

>>> setArchitecture(ARCH.X86_64)
>>> setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
>>> inst = Instruction()
>>> inst.setOpcodes("\x48\x01\xd8") # add rax, rbx
>>> inst.setAddress(0x400000)
>>> inst.updateContext(Register(REG.RAX, 0x1122334455667788))
>>> inst.updateContext(Register(REG.RBX, 0x8877665544332211))
>>> processing(inst)

>>> print inst
400000: add rax, rbx

>>> for expr in inst.getSymbolicExpressions():
...     print expr
...
ref_0 = ((0x1122334455667788 + 0x8877665544332211) & 0xFFFFFFFFFFFFFFFF) # ADD operation
ref_1 = (0x1 if (0x10 == (0x10 & (ref_0 ^ (0x1122334455667788 ^ 0x8877665544332211)))) else 0x0) # Adjust flag
ref_2 = ((((0x1122334455667788 & 0x8877665544332211) ^ (((0x1122334455667788 ^ 0x8877665544332211) ^ ref_0) & (0x1122334455667788 ^ 0x8877665544332211))) >> 63) & 0x1) # Carry flag
ref_3 = ((((0x1122334455667788 ^ ~0x8877665544332211) & (0x1122334455667788 ^ ref_0)) >> 63) & 0x1) # Overflow flag
ref_4 = ((((((((0x1 ^ (((ref_0 & 0xFF) >> 0x0) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x1) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x2) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x3) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x4) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x5) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x6) & 0x1)) ^ (((ref_0 & 0xFF) >> 0x7) & 0x1)) # Parity flag
ref_5 = ((ref_0 >> 63) & 0x1) # Sign flag
ref_6 = (0x1 if (ref_0 == 0x0) else 0x0) # Zero flag
ref_7 = 0x400003 # Program Counter
~~~~~~~~~~~~~

\section ast_py_examples_page Examples
<hr>

\subsection ast_py_examples_page_1 Get a register's expression and create an assert

~~~~~~~~~~~~~{.py}
# Get the symbolic expression of the ZF flag
zfId    = getSymbolicRegisterId(REG.ZF)
zfExpr  = getFullAst(getSymbolicExpressionFromId(zfId).getAst())

# (assert (= zf True))
newExpr = ast.assert_(
            ast.equal(
                zfExpr,
                ast.bvtrue()
            )
          )

# Get a model
models  = getModel(newExpr)
~~~~~~~~~~~~~


\subsection ast_py_examples_page_2 Play with the AST

~~~~~~~~~~~~~{.py}
# Node information

>>> node = bvadd(bv(1, 8), bvxor(bv(10, 8), bv(20, 8)))
>>> print type(node)
<type 'AstNode'>

>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

>>> subchild = node.getChilds()[1].getChilds()[0]
>>> print subchild
(_ bv10 8)

>>> print subchild.getChilds()[0].getValue()
10
>>> print subchild.getChilds()[1].getValue()
8

# Node modification

>>> node = bvadd(bv(1, 8), bvxor(bv(10, 8), bv(20, 8)))
>>> print node
(bvadd (_ bv1 8) (bvxor (_ bv10 8) (_ bv20 8)))

>>> node.setChild(0, bv(123, 8))
>>> print node
(bvadd (_ bv123 8) (bvxor (_ bv10 8) (_ bv20 8)))
~~~~~~~~~~~~~

\subsection ast_py_examples_page_3 Python operators

~~~~~~~~~~~~~{.py}
>>> a = bv(1, 8)
>>> b = bv(2, 8)
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
a \ b             | (bvsdiv a b)
a \| b            | (bvor a b)
a & b             | (bvand a b)
a ^ b             | (bvxor a b)
a % b             | (bvsmod a b)
a << b            | (bvshl a b)
a \>> b           | (bvlshr a b)
~a                | (bvnot a)
-a                | (bvneg a)

\section ast_py_api Python API - Methods of the ast module
<hr>

- **assert_(AstNode expr1)**<br>
Returns the ast `triton::ast::assert_()` representation as \ref py_AstNode_page.<br>
e.g: `(assert expr1)`.

- **bv(integer value, integer size)**<br>
Returns the ast `triton::ast::bv()` representation as \ref py_AstNode_page. The `size` is in bits.<br>
e.g: `(_ bvValue size)`.

- **bvadd(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvadd()` representation as \ref py_AstNode_page.<br>
e.g: `(bvadd expr1 epxr2)`.

- **bvand(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvand()` as \ref py_AstNode_page.<br>
e.g: `(bvand expr1 epxr2)`.

- **bvashr(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvashr()` representation as \ref py_AstNode_page.<br>
e.g: `(bvashr expr1 epxr2)`.

- **bvdecl(integer size)**<br>
Returns the ast `triton::ast::bvdecl()` representation as \ref py_AstNode_page.<br>
e.g: `(_ BitVec size)`.

- **bvfalse()**<br>
This is an alias on the `(_ bv0 1)` ast expression.

- **bvlshr(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvlshr()` representation as \ref py_AstNode_page.<br>
e.g: `(lshr expr1 epxr2)`.

- **bvmul(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvmul()` representation as \ref py_AstNode_page.<br>
e.g: `(bvmul expr1 expr2)`.

- **bvnand(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvnand()` representation as \ref py_AstNode_page.<br>
e.g: `(bvnand expr1 expr2)`.

- **bvneg(AstNode expr1)**<br>
Returns the ast `triton::ast::bvneg()` representation as \ref py_AstNode_page.<br>
e.g: `(bvneg expr1)`.

- **bvnor(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvnor()` representation as \ref py_AstNode_page.<br>
e.g: `(bvnor expr1 expr2)`.

- **bvnot(AstNode expr1)**<br>
Returns the ast `triton::ast::bvnot()` representation as \ref py_AstNode_page.<br>
e.g: `(bvnot expr1)`.

- **bvor(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvor()` representation as \ref py_AstNode_page.<br>
e.g: `(bvor expr1 expr2)`.

- **bvror(integer displacement, AstNode expr2)**<br>
Returns the ast `triton::ast::bvror()` representation as \ref py_AstNode_page.<br>
e.g: `((_ rotate_right displacement) expr)`.

- **bvrol(integer displacement, AstNode expr2)**<br>
Returns the ast `triton::ast::bvrol()` representation as \ref py_AstNode_page.<br>
e.g: `((_ rotate_left displacement) expr)`.

- **bvsdiv(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsdiv()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsdiv expr1 epxr2)`.

- **bvsge(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsge()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsge expr1 epxr2)`.

- **bvsgt(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsgt()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsgt expr1 epxr2)`.

- **bvshl(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvshl()` representation as \ref py_AstNode_page.<br>
e.g: `(bvshl expr1 expr2)`.

- **bvsle(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsle()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsle expr1 epxr2)`.

- **bvslt(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvslt()` representation as \ref py_AstNode_page.<br>
e.g: `(bvslt expr1 epxr2)`.

- **bvsmod(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsmod()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsmod expr1 expr2)`.

- **bvsrem(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsrem()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsrem expr1 expr2)`.

- **bvsub(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvsub()` representation as \ref py_AstNode_page.<br>
e.g: `(bvsub expr1 epxr2)`.

- **bvtrue()**<br>
This is an alias on the `(_ bv1 1)` ast expression.

- **bvudiv(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvudiv()` representation as \ref py_AstNode_page.<br>
e.g: `(bvudiv expr1 epxr2)`.

- **bvuge(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvuge()` representation as \ref py_AstNode_page.<br>
e.g: `(bvuge expr1 epxr2)`.

- **bvugt(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvugt()` representation as \ref py_AstNode_page.<br>
e.g: `(bvugt expr1 epxr2)`.

- **bvule(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvule()` representation as \ref py_AstNode_page.<br>
e.g: `(bvule expr1 epxr2)`.

- **bvult(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvult()` representation as \ref py_AstNode_page.<br>
e.g: `(bvult expr1 epxr2)`.

- **bvurem(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvurem()` representation as \ref py_AstNode_page.<br>
e.g: `(bvurem expr1 expr2)`.

- **bvxnor(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvxnor()` representation as \ref py_AstNode_page.<br>
e.g: `(bvxnor expr1 expr2)`.

- **bvxor(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::bvxor()` representation as \ref py_AstNode_page.<br>
e.g: `(bvxor expr1 epxr2)`.

- **compound([AstNode expr ...])**<br>
Returns the `triton::ast::compound()` node as \ref py_AstNode_page.

- **concat([AstNode expr ...])**<br>
Returns the `triton::ast::concat()` node as \ref py_AstNode_page.

- **distinct(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::distinct()` representation as \ref py_AstNode_page.<br>
e.g: `(distinct expr1 expr2)`

- **duplicate(AstNode expr)**<br>
Duplicates the node and returns a new instance as \ref py_AstNode_page. When you play with a node, it's recommended to use this function before any manipulation.

- **equal(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::equal()` representation as \ref py_AstNode_page.<br>
e.g: `(= expr1 epxr2)`.

- **extract(integer high, integer low, AstNode expr1)**<br>
Returns the ast `triton::ast::extract()` representation as \ref py_AstNode_page.<br>
e.g: `((_ extract high low) expr1)`.

- **ite(AstNode ifExpr, AstNode thenExpr, AstNode elseExpr)**<br>
Returns the ast `triton::ast::ite()` representation as \ref py_AstNode_page.<br>
e.g: `(ite ifExpr thenExpr elseExpr)`.

- **land(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::land()` representation as \ref py_AstNode_page.<br>
e.g: `(and expr1 expr2)`.

- **let(string alias, AstNode expr2, AstNode expr3)**<br>
Returns the ast `triton::ast::let()` representation as \ref py_AstNode_page.<br>
e.g: `(let ((alias expr2)) expr3)`.

- **lnot(AstNode expr)**<br>
Returns the ast `triton::ast::lnot()` representation as \ref py_AstNode_page.<br>
e.g: `(not expr)`.

- **lor(AstNode expr1, AstNode expr2)**<br>
Returns the ast `triton::ast::lor()` representation as \ref py_AstNode_page.<br>
e.g: `(or expr1 expr2)`.

- **reference(integer exprId)**<br>
Returns the reference (`triton::ast::reference()`) node representation as \ref py_AstNode_page.
Be careful, the targeted node reference is always on the max vector size, except for volatile
expressions.<br>
e.g: `ref!123`.

- **string(string s)**<br>
Returns a `triton::ast::string()` node as \ref py_AstNode_page.

- **sx(integer sizeExt, AstNode expr1)**<br>
Returns the ast `triton::ast::sx()` representation as \ref py_AstNode_page.<br>
e.g: `((_ sign_extend sizeExt) expr1)`.

- **variable(\ref py_SymbolicVariable_page symVar)**<br>
Returns a `triton::ast::variable()` node as \ref py_AstNode_page.

- **zx(integer sizeExt, AstNode expr1)**<br>
Returns the ast `triton::ast::zx()` representation as \ref py_AstNode_page.<br>
e.g: `((_ zero_extend sizeExt) expr1)`.

*/



namespace triton {
  namespace bindings {
    namespace python {


      static PyObject* ast_assert(PyObject* self, PyObject* expr) {
        if (!PyAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "assert_(): expected a AstNode as first argument");

        try {
          return PyAstNode(triton::ast::assert_(PyAstNode_AsAstNode(expr)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as first argument");

        if (op2 == nullptr || (!PyLong_Check(op2) && !PyInt_Check(op2)))
          return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as second argument");

        try {
          return PyAstNode(triton::ast::bv(PyLong_AsUint512(op1), PyLong_AsUint(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvadd(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvadd(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvadd(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvadd(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvand(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvand(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvand(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvand(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvashr(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvashr(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvashr(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvashr(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvdecl(PyObject* self, PyObject* size) {
        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "bvdecl(): expected an integer as argument");

        try {
          return PyAstNode(triton::ast::bvdecl(PyLong_AsUint(size)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvfalse(PyObject* self, PyObject* args) {
        try {
          return PyAstNode(triton::ast::bvfalse());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvlshr(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvlshr(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvmul(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvmul(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvmul(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvmul(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvnand(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnand(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvnand(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvnand(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvneg(PyObject* self, PyObject* op1) {
        if (!PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvneg(): expected a AstNode as first argument");

        try {
          return PyAstNode(triton::ast::bvneg(PyAstNode_AsAstNode(op1)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvnor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvnor(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvnor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvnot(PyObject* self, PyObject* op1) {
        if (!PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnot(): expected a AstNode as first argument");

        try {
          return PyAstNode(triton::ast::bvnot(PyAstNode_AsAstNode(op1)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvor(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvror(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected an integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvror(PyLong_AsUint(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvrol(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvrol(PyLong_AsUint(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsdiv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsdiv(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsge(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsge(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsge(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsge(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsgt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsgt(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvshl(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvshl(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvshl(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvshl(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsle(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsle(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsle(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsle(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvslt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvslt(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvslt(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvslt(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsmod(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsmod(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsrem(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsrem(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvsub(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsub(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsub(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvsub(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvtrue(PyObject* self, PyObject* args) {
        try {
          return PyAstNode(triton::ast::bvtrue());
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvudiv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvudiv(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvuge(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvuge(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvuge(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvuge(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvugt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvugt(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvugt(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvugt(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvule(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvule(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvule(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvule(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvult(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvult(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvult(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvult(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvurem(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvurem(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvurem(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvurem(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvxnor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvxnor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_bvxor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvxor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvxor(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::bvxor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_distinct(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "distinct(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "distinct(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::distinct(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_duplicate(PyObject* self, PyObject* expr) {
        if (!PyAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "duplicate(): expected a AstNode as argument");

        try {
          return PyAstNode(triton::ast::newInstance(PyAstNode_AsAstNode(expr)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_compound(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::AbstractNode *> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "compound(): expected a list of AstNodes as first argument");

        /* Check if the mems list contains only integer item and craft a std::list */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PyAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "compound(): Each element from the list must be a AstNode");

          exprs.push_back(PyAstNode_AsAstNode(item));
        }

        try {
          return PyAstNode(triton::ast::compound(exprs));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_concat(PyObject* self, PyObject* exprsList) {
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
          return PyAstNode(triton::ast::concat(exprs));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_equal(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "equal(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "equal(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::equal(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_extract(PyObject* self, PyObject* args) {
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
          return PyAstNode(triton::ast::extract(PyLong_AsUint(op1), PyLong_AsUint(op2), PyAstNode_AsAstNode(op3)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_ite(PyObject* self, PyObject* args) {
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
          return PyAstNode(triton::ast::ite(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2), PyAstNode_AsAstNode(op3)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_land(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "land(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "land(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::land(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_let(PyObject* self, PyObject* args) {
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
          return PyAstNode(triton::ast::let(PyString_AsString(op1), PyAstNode_AsAstNode(op2), PyAstNode_AsAstNode(op3)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_lnot(PyObject* self, PyObject* expr) {
        if (expr == nullptr || !PyAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "lnot(): expected a AstNode as argument");

        try {
          return PyAstNode(triton::ast::lnot(PyAstNode_AsAstNode(expr)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_lor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "lor(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "lor(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::lor(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_reference(PyObject* self, PyObject* exprId) {
        if (!PyInt_Check(exprId) && !PyLong_Check(exprId))
          return PyErr_Format(PyExc_TypeError, "reference(): expected an integer as argument");

        if (!triton::api.isSymbolicExpressionIdExists(PyLong_AsUint(exprId)))
          return PyErr_Format(PyExc_TypeError, "reference(): symbolic expression id not found");

        try {
          return PyAstNode(triton::ast::reference(PyLong_AsUint(exprId)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_string(PyObject* self, PyObject* expr) {
        if (!PyString_Check(expr))
          return PyErr_Format(PyExc_TypeError, "string(): expected a string as first argument");

        try {
          return PyAstNode(triton::ast::string(PyString_AsString(expr)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_sx(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "sx(): expected an integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "sx(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::sx(PyLong_AsUint(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_variable(PyObject* self, PyObject* symVar) {
        if (!PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "variable(): expected a SymbolicVariable as first argument");

        try {
          return PyAstNode(triton::ast::variable(*PySymbolicVariable_AsSymbolicVariable(symVar)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* ast_zx(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "zx(): expected an integer as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "zx(): expected a AstNode as second argument");

        try {
          return PyAstNode(triton::ast::zx(PyLong_AsUint(op1), PyAstNode_AsAstNode(op2)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      PyMethodDef astCallbacks[] = {
        {"assert_",     (PyCFunction)ast_assert,     METH_O,           ""},
        {"bv",          (PyCFunction)ast_bv,         METH_VARARGS,     ""},
        {"bvadd",       (PyCFunction)ast_bvadd,      METH_VARARGS,     ""},
        {"bvand",       (PyCFunction)ast_bvand,      METH_VARARGS,     ""},
        {"bvashr",      (PyCFunction)ast_bvashr,     METH_VARARGS,     ""},
        {"bvdecl",      (PyCFunction)ast_bvdecl,     METH_O,           ""},
        {"bvfalse",     (PyCFunction)ast_bvfalse,    METH_NOARGS,      ""},
        {"bvlshr",      (PyCFunction)ast_bvlshr,     METH_VARARGS,     ""},
        {"bvmul",       (PyCFunction)ast_bvmul,      METH_VARARGS,     ""},
        {"bvnand",      (PyCFunction)ast_bvnand,     METH_VARARGS,     ""},
        {"bvneg",       (PyCFunction)ast_bvneg,      METH_O,           ""},
        {"bvnor",       (PyCFunction)ast_bvnor,      METH_VARARGS,     ""},
        {"bvnot",       (PyCFunction)ast_bvnot,      METH_O,           ""},
        {"bvor",        (PyCFunction)ast_bvor,       METH_VARARGS,     ""},
        {"bvrol",       (PyCFunction)ast_bvrol,      METH_VARARGS,     ""},
        {"bvror",       (PyCFunction)ast_bvror,      METH_VARARGS,     ""},
        {"bvsdiv",      (PyCFunction)ast_bvsdiv,     METH_VARARGS,     ""},
        {"bvsge",       (PyCFunction)ast_bvsge,      METH_VARARGS,     ""},
        {"bvsgt",       (PyCFunction)ast_bvsgt,      METH_VARARGS,     ""},
        {"bvshl",       (PyCFunction)ast_bvshl,      METH_VARARGS,     ""},
        {"bvsle",       (PyCFunction)ast_bvsle,      METH_VARARGS,     ""},
        {"bvslt",       (PyCFunction)ast_bvslt,      METH_VARARGS,     ""},
        {"bvsmod",      (PyCFunction)ast_bvsmod,     METH_VARARGS,     ""},
        {"bvsrem",      (PyCFunction)ast_bvsrem,     METH_VARARGS,     ""},
        {"bvsub",       (PyCFunction)ast_bvsub,      METH_VARARGS,     ""},
        {"bvtrue",      (PyCFunction)ast_bvtrue,     METH_NOARGS,      ""},
        {"bvudiv",      (PyCFunction)ast_bvudiv,     METH_VARARGS,     ""},
        {"bvuge",       (PyCFunction)ast_bvuge,      METH_VARARGS,     ""},
        {"bvugt",       (PyCFunction)ast_bvugt,      METH_VARARGS,     ""},
        {"bvule",       (PyCFunction)ast_bvule,      METH_VARARGS,     ""},
        {"bvult",       (PyCFunction)ast_bvult,      METH_VARARGS,     ""},
        {"bvurem",      (PyCFunction)ast_bvurem,     METH_VARARGS,     ""},
        {"bvxnor",      (PyCFunction)ast_bvxnor,     METH_VARARGS,     ""},
        {"bvxor",       (PyCFunction)ast_bvxor,      METH_VARARGS,     ""},
        {"compound",    (PyCFunction)ast_compound,   METH_O,           ""},
        {"concat",      (PyCFunction)ast_concat,     METH_O,           ""},
        {"distinct",    (PyCFunction)ast_distinct,   METH_VARARGS,     ""},
        {"duplicate",   (PyCFunction)ast_duplicate,  METH_O,           ""},
        {"equal",       (PyCFunction)ast_equal,      METH_VARARGS,     ""},
        {"extract",     (PyCFunction)ast_extract,    METH_VARARGS,     ""},
        {"ite",         (PyCFunction)ast_ite,        METH_VARARGS,     ""},
        {"land",        (PyCFunction)ast_land,       METH_VARARGS,     ""},
        {"let",         (PyCFunction)ast_let,        METH_VARARGS,     ""},
        {"lnot",        (PyCFunction)ast_lnot,       METH_O,           ""},
        {"lor",         (PyCFunction)ast_lor,        METH_VARARGS,     ""},
        {"reference",   (PyCFunction)ast_reference,  METH_O,           ""},
        {"string",      (PyCFunction)ast_string,     METH_O,           ""},
        {"sx",          (PyCFunction)ast_sx,         METH_VARARGS,     ""},
        {"variable",    (PyCFunction)ast_variable,   METH_O,           ""},
        {"zx",          (PyCFunction)ast_zx,         METH_VARARGS,     ""},
        {nullptr,       nullptr,                     0,                nullptr}
      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */

