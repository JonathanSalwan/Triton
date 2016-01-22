//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <pythonUtils.hpp>
#include <smt2lib.hpp>
#include <pythonObjects.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_smt2lib_page SMT2-Lib
    \brief [**python api**] All information about the smt2lib python module.
    \anchor smt2lib

\tableofcontents

\section smt2lib_py_description Description
<hr>

The [SMT-LIB](http://smtlib.cs.uiowa.edu/) is an international initiative aimed at facilitating research and development in Satisfiability Modulo Theories (SMT).

~~~~~~~~~~~~~{.py}
>>> from triton import smt2lib
>>> smt2lib
<module 'smt2lib' (built-in)>
~~~~~~~~~~~~~

Triton uses the SMT2-Lib to represent the instruction's semantics. Then, via the API you will be able to build and to modify your own symbolic expressions.

~~~~~~~~~~~~~{.asm}
Instruction:  add rax, rdx
Expression:   #41 = (bvadd ((_ extract 63 0) #40) ((_ extract 63 0) #39))
~~~~~~~~~~~~~

As all Triton's expressions are on [SSA form](http://en.wikipedia.org/wiki/Static_single_assignment_form), the id `#41` is the new expression of the `RAX`
register, the id `#40` is the previous expression of the `RAX` register and the id `#39` is the previous expression of the `RDX` register.
An \ref py_Instruction_page may contain several expressions (\ref py_SymbolicExpression_page). For example, the previous `add rax, rdx` instruction contains
7 expressions: 1 `ADD` semantics and 6 flags (`AF, CF, OF, PF, SF and ZF`) semantics where each flag is stored in a new \ref py_SymbolicExpression_page.

~~~~~~~~~~~~~{.asm}
Instruction: add rax, rdx
Expressions: #41 = (bvadd ((_ extract 63 0) #40) ((_ extract 63 0) #39))
             #42 = (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor #41 (bvxor ((_ extract 63 0) #40) ((_ extract 63 0) #39))))) (_ bv1 1) (_ bv0 1))
             #43 = (ite (bvult #41 ((_ extract 63 0) #40)) (_ bv1 1) (_ bv0 1))
             #44 = (ite (= ((_ extract 63 63) (bvand (bvxor ((_ extract 63 0) #40) (bvnot ((_ extract 63 0) #39))) (bvxor ((_ extract 63 0) #40) #41))) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
             #45 = (ite (= (parity_flag ((_ extract 7 0) #41)) (_ bv0 1)) (_ bv1 1) (_ bv0 1))
             #46 = (ite (= ((_ extract 63 63) #41) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
             #47 = (ite (= #41 (_ bv0 64)) (_ bv1 1) (_ bv0 1))
~~~~~~~~~~~~~

Triton deals with 64-bits registers (and 128-bits for SSE). It means that it uses the `concat` and `extract` functions when operations are performed on subregister.

~~~~~~~~~~~~~{.asm}
mov al, 0xff  -> #193 = (concat ((_ extract 63 8) #191) (_ bv255 8))
movsx eax, al -> #195 = ((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) #193)))
~~~~~~~~~~~~~

On the line 1, a new 64bit-vector is created with the concatenation of `RAX[63..8]` and the concretization of the value `0xff`. On the line 2, according
to the AMD64 behavior, if a 32-bit register is written, the CPU clears the 32-bit MSB of the corresponding register. So, in this case, we apply a sign
extension from al to `EAX`, then a zero extension from `EAX` to `RAX`.

\section ast_representation AST representation
<hr>

An abstract syntax tree ([AST](https://en.wikipedia.org/wiki/Abstract_syntax_tree)) is a representation of a grammar as tree. Triton uses its own SMT
representation as AST for all symbolic expressions. As all SMT expressions are built at runtime, an AST is available at each program point. For example,
let assume this set of instructions:

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
your own AST or to modify an AST given by Triton and perform some modifications and simplifications before sending it to the solver.

\section ast_grammar The SMT's grammar slightly modified

To manage easiest the subgraphs and to keep the SSA form of registers and memory, we have been constraint to modify slightly the grammar
of the SMT. Actually, only one kind of node has been added in the grammar. We have added a `REFERENCE` node which is a "terminate" node of a
graph but contains a reference to a subgraph. Below an example of one "partial" graph linked with two others subgraphs.

<p align="center"><img width="600" src="http://triton.quarkslab.com/files/smt_ast_ref.svg"/></p>

If you try to go through the full AST you will fail at the first reference node because a reference node does not contains child nodes.
The only way to jump from a reference node to the targeted node is to use the triton::engines::symbolic::SymbolicEngine::getFullAst() function.

~~~~~~~~~~~~~{.py}
[IN]  zfId = getSymbolicRegisterId(REG.ZF)
[IN]  partialGraph = getSymbolicExpressionFromId(zfId).getAst()
[IN]  print partialGraph
[OUT] (ite (= #89 (_ bv0 32)) (_ bv1 1) (_ bv0 1))

[IN]  fullGraph = getFullAst(partialGraph)
[IN]  print fullGraph
[OUT] (ite (= (bvsub ((_ extract 31 0) ((_ zero_extend 32) ((_ extract 31 0) ((_ zero_extend 32) (bvxor ((_ extract 31 0) ((_ zero_extend 32) (bvsub ((_ extract 31 0) ((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) SymVar_0)))) (_ bv1 32)))) (_ bv85 32)))))) ((_ extract 31 0) ((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (_ bv49 8))))))))) (_ bv0 32)) (_ bv1 1) (_ bv0 1))
~~~~~~~~~~~~~

\section smt2lib_py_example Examples
<hr>

\subsection smt2lib_py_example_1 Get a register's expression and create an assert

~~~~~~~~~~~~~{.py}
# Get the symbolic expression of the ZF flag
zfId    = getSymbolicRegisterId(REG.ZF)
zfExpr  = getFullAst(getSymbolicExpressionFromId(zfId).getAst())

# (assert (= zf True))
newExpr = smt2lib.smtAssert(
            smt2lib.equal(
                zfExpr,
                smt2lib.bvtrue()
            )
          )

# Get a model
models  = getModel(newExpr)
~~~~~~~~~~~~~


\subsection smt2lib_py_example_2 Play with the AST

~~~~~~~~~~~~~{.py}
# Node information

>>> node = bvadd(bv(1, 8), bvxor(bv(10, 8), bv(20, 8)))
>>> print type(node)
<type 'SmtAstNode'>

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

\subsection smt2lib_py_example_3 Python operators

~~~~~~~~~~~~~{.py}
>>> a = bv(1, 8)
>>> b = bv(2, 8)
>>> c = (a & ~b) | (~a & b)
>>> print c
(bvor (bvand (_ bv1 8) (bvnot (_ bv2 8))) (bvand (bvnot (_ bv1 8)) (_ bv2 8)))
~~~~~~~~~~~~~

As we can't overload all SMT2-Lib's operators only these following operators are overloaded:

Python's Operator | SMT2-Lib format
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

\section smt2lib_py_api Python API - Methods of the smt2lib module
<hr>

- **bv(integer value, integer size)**<br>
Returns the smt2-lib `triton::smt2lib::bv()` syntax as \ref py_SmtAstNode_page. The `size` is in bits.<br>
e.g: `(_ bvValue size)`.

- **bvadd(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvadd()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvadd expr1 epxr2)`.

- **bvand(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib syntax `triton::smt2lib::bvand()` as \ref py_SmtAstNode_page.<br>
e.g: `(bvand expr1 epxr2)`.

- **bvashr(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvashr()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvashr expr1 epxr2)`.

- **bvfalse()**<br>
This is an alias on the `(_ bv0 1)` smt2-lib expression.

- **bvlshr(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvlshr()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(lshr expr1 epxr2)`.

- **bvmul(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvmul()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvmul expr1 expr2)`.

- **bvnand(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvnand()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvnand expr1 expr2)`.

- **bvneg(SmtAstNode expr1)**<br>
Returns the smt2-lib `triton::smt2lib::bvneg()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvneg expr1)`.

- **bvnor(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvnor()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvnor expr1 expr2)`.

- **bvnot(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvnot()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvnot expr1)`.

- **bvor(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvor()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvor expr1 expr2)`.

- **bvror(integer displacement, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvror()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `((_ rotate_right displacement) expr)`.

- **bvrol(integer displacement, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvrol()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `((_ rotate_left displacement) expr)`.

- **bvsdiv(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsdiv()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsdiv expr1 epxr2)`.

- **bvsge(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsge()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsge expr1 epxr2)`.

- **bvsgt(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsgt()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsgt expr1 epxr2)`.

- **bvshl(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvshl()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvshl expr1 expr2)`.

- **bvsle(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsle()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsle expr1 epxr2)`.

- **bvslt(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvslt()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvslt expr1 epxr2)`.

- **bvsmod(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsmod()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsmod expr1 expr2)`.

- **bvsrem(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsrem()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsrem expr1 expr2)`.

- **bvsub(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvsub()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvsub expr1 epxr2)`.

- **bvtrue()**<br>
This is an alias on the `(_ bv1 1)` smt2-lib expression.

- **bvudiv(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvudiv()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvudiv expr1 epxr2)`.

- **bvuge(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvuge()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvuge expr1 epxr2)`.

- **bvugt(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvugt()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvugt expr1 epxr2)`.

- **bvule(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvule()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvule expr1 epxr2)`.

- **bvult(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvult()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvult expr1 epxr2)`.

- **bvurem(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvurem()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvurem expr1 expr2)`.

- **bvxnor(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvxnor()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvxnor expr1 expr2)`.

- **bvxor(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::bvxor()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(bvxor expr1 epxr2)`.

- **compound([SmtAstNode expr ...])**<br>
Returns the `triton::smt2lib::compound()` node as \ref py_SmtAstNode_page.

- **concat([SmtAstNode expr ...])**<br>
Returns the `triton::smt2lib::concat()` node as \ref py_SmtAstNode_page.

- **distinct(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::distinct()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(distinct expr1 expr2)`

- **equal(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::equal()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(= expr1 epxr2)`.

- **extract(integer high, integer low, SmtAstNode expr1)**<br>
Returns the smt2-lib `triton::smt2lib::extract()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `((_ extract high low) expr1)`.

- **ite(SmtAstNode ifExpr, SmtAstNode thenExpr, SmtAstNode elseExpr)**<br>
Returns the smt2-lib `triton::smt2lib::ite()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(ite ifExpr thenExpr elseExpr)`.

- **land(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::land()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(and expr1 expr2)`.

- **lnot(SmtAstNode expr)**<br>
Returns the smt2-lib `triton::smt2lib::lnot()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(not expr)`.

- **lor(SmtAstNode expr1, SmtAstNode expr2)**<br>
Returns the smt2-lib `triton::smt2lib::lor()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(or expr1 expr2)`.

- **reference(integer exprId)**<br>
Returns the reference (`triton::smt2lib::reference()`) node syntax as \ref py_SmtAstNode_page.
Be careful, the targeted node reference is always on the max vector size, except for volatile
expressions.<br>
e.g: `#123`.

- **smtAssert(SmtAstNode expr1)**<br>
Returns the smt2-lib `triton::smt2lib::smtAssert()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `(assert expr1)`.

- **string(string s)**<br>
Returns a `triton::smt2lib::string()` node as \ref py_SmtAstNode_page.

- **sx(integer sizeExt, SmtAstNode expr1)**<br>
Returns the smt2-lib `triton::smt2lib::sx()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `((_ sign_extend sizeExt) expr1)`.

- **variable(string s)**<br>
Returns a `triton::smt2lib::variable()` node as \ref py_SmtAstNode_page.

- **zx(integer sizeExt, SmtAstNode expr1)**<br>
Returns the smt2-lib `triton::smt2lib::zx()` syntax as \ref py_SmtAstNode_page.<br>
e.g: `((_ zero_extend sizeExt) expr1)`.

*/



namespace triton {
  namespace bindings {
    namespace python {


      static PyObject* smt2lib_bv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as first argument");

        if (op2 == nullptr || (!PyLong_Check(op2) && !PyInt_Check(op2)))
          return PyErr_Format(PyExc_TypeError, "bv(): expected an integer as second argument");

        return PySmtAstNode(smt2lib::bv(PyLong_AsUint128(op1), PyLong_AsUint(op2)));
      }


      static PyObject* smt2lib_bvadd(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvadd(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvadd(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvadd(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvand(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvand(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvand(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvand(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvashr(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvashr(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvashr(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvashr(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvfalse(PyObject* self, PyObject* args) {
        return PySmtAstNode(smt2lib::bvfalse());
      }


      static PyObject* smt2lib_bvlshr(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvlshr(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvlshr(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvmul(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvmul(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvmul(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvmul(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvnand(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnand(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvnand(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvnand(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvneg(PyObject* self, PyObject* op1) {
        if (!PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvneg(): expected a SmtAstNode as first argument");

        return PySmtAstNode(smt2lib::bvneg(PySmtAstNode_AsSmtAstNode(op1)));
      }


      static PyObject* smt2lib_bvnor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnor(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvnor(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvnor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvnot(PyObject* self, PyObject* op1) {
        if (!PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvnot(): expected a SmtAstNode as first argument");

        return PySmtAstNode(smt2lib::bvnot(PySmtAstNode_AsSmtAstNode(op1)));
      }


      static PyObject* smt2lib_bvor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvor(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvor(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvror(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected an integer as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvror(PyLong_AsUint(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvrol(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a integer as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvrol(PyLong_AsUint(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsdiv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsdiv(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsdiv(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsge(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsge(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsge(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsge(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsgt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsgt(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsgt(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvshl(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvshl(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvshl(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvshl(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsle(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsle(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsle(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsle(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvslt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvslt(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvslt(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvslt(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsmod(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsmod(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsmod(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsrem(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsrem(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsrem(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvsub(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvsub(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvsub(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvsub(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvtrue(PyObject* self, PyObject* args) {
        return PySmtAstNode(smt2lib::bvtrue());
      }


      static PyObject* smt2lib_bvudiv(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvudiv(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvudiv(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvuge(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvuge(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvuge(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvuge(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvugt(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvugt(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvugt(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvugt(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvule(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvule(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvule(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvule(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvult(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvult(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvult(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvult(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvurem(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvurem(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvurem(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvurem(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvxnor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvxnor(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvxnor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_bvxor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvxor(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvxor(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::bvxor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_distinct(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "distinct(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "distinct(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::distinct(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_compound(PyObject* self, PyObject* exprsList) {
        std::vector<smt2lib::smtAstAbstractNode *> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "compound(): expected a list of SmtAstNodes as first argument");

        /* Check if the mems list contains only integer item and craft a std::list */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PySmtAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "compound(): Each element from the list must be a SmtAstNode");

          exprs.push_back(PySmtAstNode_AsSmtAstNode(item));
        }

        return PySmtAstNode(smt2lib::compound(exprs));
      }


      static PyObject* smt2lib_concat(PyObject* self, PyObject* exprsList) {
        std::vector<smt2lib::smtAstAbstractNode *> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "concat(): expected a list of SmtAstNodes as first argument");

        /* Check if the list contains only PySmtAstNode */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PySmtAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "concat(): Each element from the list must be a SmtAstNode");

          exprs.push_back(PySmtAstNode_AsSmtAstNode(item));
        }

        return PySmtAstNode(smt2lib::concat(exprs));
      }


      static PyObject* smt2lib_equal(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "equal(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "equal(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::equal(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_extract(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        PyObject* op3 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2, &op3);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "extract(): expected an integer as first argument");

        if (op2 == nullptr || (!PyLong_Check(op2) && !PyInt_Check(op2)))
          return PyErr_Format(PyExc_TypeError, "extract(): expected an integer as second argument");

        if (op3 == nullptr || !PySmtAstNode_Check(op3))
          return PyErr_Format(PyExc_TypeError, "extract(): expected a SmtAstNode as third argument");

        return PySmtAstNode(smt2lib::extract(PyLong_AsUint(op1), PyLong_AsUint(op2), PySmtAstNode_AsSmtAstNode(op3)));
      }


      static PyObject* smt2lib_ite(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        PyObject* op3 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2, &op3);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "ite(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "ite(): expected a SmtAstNode as second argument");

        if (op3 == nullptr || !PySmtAstNode_Check(op3))
          return PyErr_Format(PyExc_TypeError, "ite(): expected a SmtAstNode as third argument");

        return PySmtAstNode(smt2lib::ite(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2), PySmtAstNode_AsSmtAstNode(op3)));
      }


      static PyObject* smt2lib_land(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "land(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "land(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::land(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_lnot(PyObject* self, PyObject* expr) {
        if (expr == nullptr || !PySmtAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "lnot(): expected a SmtAstNode as argument");

        return PySmtAstNode(smt2lib::lnot(PySmtAstNode_AsSmtAstNode(expr)));
      }


      static PyObject* smt2lib_lor(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &op1, &op2);

        if (op1 == nullptr || !PySmtAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "lor(): expected a SmtAstNode as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "lor(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::lor(PySmtAstNode_AsSmtAstNode(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_reference(PyObject* self, PyObject* exprId) {
        if (!PyInt_Check(exprId) && !PyLong_Check(exprId))
          return PyErr_Format(PyExc_TypeError, "reference(): expected an integer as argument");

        if (!triton::api.isSymbolicExpressionIdExists(PyLong_AsUint(exprId)))
          return PyErr_Format(PyExc_TypeError, "reference(): symbolic expression id not found");

        return PySmtAstNode(smt2lib::reference(PyLong_AsUint(exprId)));
      }


      static PyObject* smt2lib_smtAssert(PyObject* self, PyObject* expr) {
        if (!PySmtAstNode_Check(expr))
          return PyErr_Format(PyExc_TypeError, "smtAssert(): expected a SmtAstNode as first argument");

        return PySmtAstNode(smt2lib::smtAssert(PySmtAstNode_AsSmtAstNode(expr)));
      }


      static PyObject* smt2lib_string(PyObject* self, PyObject* expr) {
        if (!PyString_Check(expr))
          return PyErr_Format(PyExc_TypeError, "string(): expected a string as first argument");

        return PySmtAstNode(smt2lib::string(PyString_AsString(expr)));
      }


      static PyObject* smt2lib_sx(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "sx(): expected an integer as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "sx(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::sx(PyLong_AsUint(op1), PySmtAstNode_AsSmtAstNode(op2)));
      }


      static PyObject* smt2lib_variable(PyObject* self, PyObject* expr) {
        if (!PyString_Check(expr))
          return PyErr_Format(PyExc_TypeError, "variable(): expected a string as first argument");

        return PySmtAstNode(smt2lib::variable(PyString_AsString(expr)));
      }


      static PyObject* smt2lib_zx(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || (!PyLong_Check(op1) && !PyInt_Check(op1)))
          return PyErr_Format(PyExc_TypeError, "zx(): expected an integer as first argument");

        if (op2 == nullptr || !PySmtAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "zx(): expected a SmtAstNode as second argument");

        return PySmtAstNode(smt2lib::zx(PyLong_AsUint(op2), PySmtAstNode_AsSmtAstNode(op2)));
      }


      PyMethodDef smt2libCallbacks[] = {
        {"bv",          (PyCFunction)smt2lib_bv,         METH_VARARGS,     ""},
        {"bvadd",       (PyCFunction)smt2lib_bvadd,      METH_VARARGS,     ""},
        {"bvand",       (PyCFunction)smt2lib_bvand,      METH_VARARGS,     ""},
        {"bvashr",      (PyCFunction)smt2lib_bvashr,     METH_VARARGS,     ""},
        {"bvfalse",     (PyCFunction)smt2lib_bvfalse,    METH_NOARGS,      ""},
        {"bvlshr",      (PyCFunction)smt2lib_bvlshr,     METH_VARARGS,     ""},
        {"bvmul",       (PyCFunction)smt2lib_bvmul,      METH_VARARGS,     ""},
        {"bvnand",      (PyCFunction)smt2lib_bvnand,     METH_VARARGS,     ""},
        {"bvneg",       (PyCFunction)smt2lib_bvneg,      METH_O,           ""},
        {"bvnor",       (PyCFunction)smt2lib_bvnor,      METH_VARARGS,     ""},
        {"bvnot",       (PyCFunction)smt2lib_bvnot,      METH_O,           ""},
        {"bvor",        (PyCFunction)smt2lib_bvor,       METH_VARARGS,     ""},
        {"bvrol",       (PyCFunction)smt2lib_bvrol,      METH_VARARGS,     ""},
        {"bvror",       (PyCFunction)smt2lib_bvror,      METH_VARARGS,     ""},
        {"bvsdiv",      (PyCFunction)smt2lib_bvsdiv,     METH_VARARGS,     ""},
        {"bvsge",       (PyCFunction)smt2lib_bvsge,      METH_VARARGS,     ""},
        {"bvsgt",       (PyCFunction)smt2lib_bvsgt,      METH_VARARGS,     ""},
        {"bvshl",       (PyCFunction)smt2lib_bvshl,      METH_VARARGS,     ""},
        {"bvsle",       (PyCFunction)smt2lib_bvsle,      METH_VARARGS,     ""},
        {"bvslt",       (PyCFunction)smt2lib_bvslt,      METH_VARARGS,     ""},
        {"bvsmod",      (PyCFunction)smt2lib_bvsmod,     METH_VARARGS,     ""},
        {"bvsrem",      (PyCFunction)smt2lib_bvsrem,     METH_VARARGS,     ""},
        {"bvsub",       (PyCFunction)smt2lib_bvsub,      METH_VARARGS,     ""},
        {"bvtrue",      (PyCFunction)smt2lib_bvtrue,     METH_NOARGS,      ""},
        {"bvudiv",      (PyCFunction)smt2lib_bvudiv,     METH_VARARGS,     ""},
        {"bvuge",       (PyCFunction)smt2lib_bvuge,      METH_VARARGS,     ""},
        {"bvugt",       (PyCFunction)smt2lib_bvugt,      METH_VARARGS,     ""},
        {"bvule",       (PyCFunction)smt2lib_bvule,      METH_VARARGS,     ""},
        {"bvult",       (PyCFunction)smt2lib_bvult,      METH_VARARGS,     ""},
        {"bvurem",      (PyCFunction)smt2lib_bvurem,     METH_VARARGS,     ""},
        {"bvxnor",      (PyCFunction)smt2lib_bvxnor,     METH_VARARGS,     ""},
        {"bvxor",       (PyCFunction)smt2lib_bvxor,      METH_VARARGS,     ""},
        {"distinct",    (PyCFunction)smt2lib_distinct,   METH_VARARGS,     ""},
        {"compound",    (PyCFunction)smt2lib_compound,   METH_O,           ""},
        {"concat",      (PyCFunction)smt2lib_concat,     METH_O,           ""},
        {"equal",       (PyCFunction)smt2lib_equal,      METH_VARARGS,     ""},
        {"extract",     (PyCFunction)smt2lib_extract,    METH_VARARGS,     ""},
        {"ite",         (PyCFunction)smt2lib_ite,        METH_VARARGS,     ""},
        {"land",        (PyCFunction)smt2lib_land,       METH_VARARGS,     ""},
        {"lnot",        (PyCFunction)smt2lib_lnot,       METH_O,           ""},
        {"lor",         (PyCFunction)smt2lib_lor,        METH_VARARGS,     ""},
        {"reference",   (PyCFunction)smt2lib_reference,  METH_O,           ""},
        {"smtAssert",   (PyCFunction)smt2lib_smtAssert,  METH_O,           ""},
        {"string",      (PyCFunction)smt2lib_string,     METH_O,           ""},
        {"sx",          (PyCFunction)smt2lib_sx,         METH_VARARGS,     ""},
        {"variable",    (PyCFunction)smt2lib_variable,   METH_O,           ""},
        {"zx",          (PyCFunction)smt2lib_zx,         METH_VARARGS,     ""},
        {nullptr,       nullptr,                         0,                nullptr}
      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */

