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
#ifdef Z3_INTERFACE
  #include <triton/tritonToZ3Ast.hpp>
#endif



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
    \brief [**python api**] All information about the AstContext python object.

\tableofcontents

\section ast_description Description
<hr>

Triton converts the x86, x86-64 and AArch64 instruction set architecture into an AST representation. The class is used
to build your own AST nodes.

\anchor ast
\section AstContext_py_api Python API - Methods of the AstContext class
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
Creates a `bvashr` node (arithmetic shift right).<br>
e.g: `(bvashr expr1 epxr2)`.

- <b>\ref py_AstNode_page bvfalse(void)</b><br>
This is an alias on the `(_ bv0 1)` ast expression.

- <b>\ref py_AstNode_page bvlshr(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvlshr` node (logical shift right).<br>
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

- <b>\ref py_AstNode_page bvror(\ref py_AstNode_page expr, \ref py_AstNode_page rot)</b><br>
Creates a `bvror` node (rotate right).<br>
e.g: `((_ rotate_right rot) expr)`.

- <b>\ref py_AstNode_page bvrol(\ref py_AstNode_page expr, \ref py_AstNode_page rot)</b><br>
Creates a `bvrol` node (rotate left).<br>
e.g: `((_ rotate_left rot) expr)`.

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
Creates a Bvshl node (shift left).<br>
e.g: `(bvshl expr1 expr2)`.

- <b>\ref py_AstNode_page bvsle(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsle` node.<br>
e.g: `(bvsle expr1 epxr2)`.

- <b>\ref py_AstNode_page bvslt(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvslt` node.<br>
e.g: `(bvslt expr1 epxr2)`.

- <b>\ref py_AstNode_page bvsmod(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsmod` node (2's complement signed remainder, sign follows divisor).<br>
e.g: `(bvsmod expr1 expr2)`.

- <b>\ref py_AstNode_page bvsrem(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvsrem` node (2's complement signed remainder, sign follows dividend).<br>
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
Creates a `bvurem` node (unsigned remainder).<br>
e.g: `(bvurem expr1 expr2)`.

- <b>\ref py_AstNode_page bvxnor(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvxnor` node.<br>
e.g: `(bvxnor expr1 expr2)`.

- <b>\ref py_AstNode_page bvxor(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `bvxor` node.<br>
e.g: `(bvxor expr1 epxr2)`.

- <b>\ref py_AstNode_page concat([\ref py_AstNode_page, ...])</b><br>
Concatenates several nodes.

- <b>\ref py_AstNode_page distinct(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates a `distinct` node.<br>
e.g: `(distinct expr1 expr2)`

- <b>\ref py_AstNode_page equal(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates an `equal` node.<br>
e.g: `(= expr1 epxr2)`.

- <b>\ref py_AstNode_page extract(integer high, integer low, \ref py_AstNode_page expr1)</b><br>
Creates an `extract` node. The `high` and `low` fields represent the bits position.<br>
e.g: `((_ extract high low) expr1)`.

- <b>\ref py_AstNode_page iff(\ref py_AstNode_page expr1, \ref py_AstNode_page expr2)</b><br>
Creates an `iff` node (if and only if).<br>
e.g: `(iff expr1 expr2)`.

- <b>\ref py_AstNode_page ite(\ref py_AstNode_page ifExpr, \ref py_AstNode_page thenExpr, \ref py_AstNode_page elseExpr)</b><br>
Creates an `ite` node (if-then-else node).<br>
e.g: `(ite ifExpr thenExpr elseExpr)`.

- <b>\ref py_AstNode_page land([\ref py_AstNode_page, ...])</b><br>
Creates a logical `AND` on several nodes.
e.g: `(and expr1 expr2 expr3 expr4)`.

- <b>\ref py_AstNode_page let(string alias, \ref py_AstNode_page expr2, \ref py_AstNode_page expr3)</b><br>
Creates a `let` node.<br>
e.g: `(let ((alias expr2)) expr3)`.

- <b>\ref py_AstNode_page lnot(\ref py_AstNode_page expr)</b><br>
Creates a `lnot` node (logical NOT).<br>
e.g: `(not expr)`.

- <b>\ref py_AstNode_page lor([\ref py_AstNode_page, ...])</b><br>
Creates a logical `OR` on several nodes.
e.g: `(or expr1 expr2 expr3 expr4)`.

- <b>\ref py_AstNode_page reference(\ref py_SymbolicExpression_page expr)</b><br>
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


\section AstContext_convert_py_api Python API - Utility methods of the AstContext class
<hr>

- <b>\ref py_AstNode_page duplicate(\ref py_AstNode_page expr)</b><br>
Duplicates the node and returns a new instance as \ref py_AstNode_page.

- <b>[\ref py_AstNode_page, ...] lookingForNodes(\ref py_AstNode_page expr, \ref py_AST_NODE_page match)</b><br>
Returns a list of collected matched nodes via a depth-first pre order traversal.

- <b>z3::expr tritonToZ3(\ref py_AstNode_page expr)</b><br>
Convert a Triton AST to a Z3 AST.

- <b>\ref py_AstNode_page unrollAst(\ref py_AstNode_page node)</b><br>
Unrolls the SSA form of a given AST.


\section ast_py_examples_page_3 Python API - Operators
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

\section ast_smt_python_page The SMT or Python Syntax
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

~~~~~~~~~~~~~

*/


namespace triton {
  namespace bindings {
    namespace python {


      static PyObject* AstContext_assert(PyObject* self, PyObject* op1) {
        if (!PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "assert_(): expected a AstNode as first argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->assert_(PyAstNode_AsAstNode(op1)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


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

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvror(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvror(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
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

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "bvrol(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->bvrol(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
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


      static PyObject* AstContext_declare(PyObject* self, PyObject* var) {
        if (!PyAstNode_Check(var))
          return PyErr_Format(PyExc_TypeError, "duplicate(): expected a AstNode as argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->declare(PyAstNode_AsAstNode(var)));
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
          return PyAstNode(triton::ast::newInstance(PyAstNode_AsAstNode(expr).get()));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_compound(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::SharedAbstractNode> exprs;

        if (exprsList == nullptr || !PyList_Check(exprsList))
          return PyErr_Format(PyExc_TypeError, "compound(): expected a list of AstNodes as first argument");

        /* Check if the list contains only PyAstNode */
        for (Py_ssize_t i = 0; i < PyList_Size(exprsList); i++){
          PyObject* item = PyList_GetItem(exprsList, i);

          if (!PyAstNode_Check(item))
            return PyErr_Format(PyExc_TypeError, "compound(): Each element from the list must be a AstNode");

          exprs.push_back(PyAstNode_AsAstNode(item));
        }

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->compound(exprs));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_concat(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::SharedAbstractNode> exprs;

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


      static PyObject* AstContext_iff(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "iff(): expected a AstNode as first argument");

        if (op2 == nullptr || !PyAstNode_Check(op2))
          return PyErr_Format(PyExc_TypeError, "iff(): expected a AstNode as second argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->iff(PyAstNode_AsAstNode(op1), PyAstNode_AsAstNode(op2)));
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
        std::vector<triton::ast::SharedAbstractNode> exprs;

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


      static PyObject* AstContext_lookingForNodes(PyObject* self, PyObject* args) {
        PyObject* ret = nullptr;
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &op1, &op2);

        if (op1 == nullptr || !PyAstNode_Check(op1))
          return PyErr_Format(PyExc_TypeError, "lookingForNodes(): expected a AstNode object as first argument");

        if (op2 == nullptr || (!PyLong_Check(op2) && !PyInt_Check(op2)))
          return PyErr_Format(PyExc_TypeError, "lookingForNodes(): expected a AST_NODE enum as second argument");

        try {
          auto nodes = triton::ast::lookingForNodes(PyAstNode_AsAstNode(op1), static_cast<triton::ast::ast_e>(PyLong_AsUint32(op2)));
          ret = xPyList_New(nodes.size());

          triton::uint32 index = 0;
          for (auto&& node : nodes)
            PyList_SetItem(ret, index++, PyAstNode(node));

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_lor(PyObject* self, PyObject* exprsList) {
        std::vector<triton::ast::SharedAbstractNode> exprs;

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
          return PyAstNode(PyAstContext_AsAstContext(self)->reference(PySymbolicExpression_AsSymbolicExpression(symExpr)));
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


      static PyObject* AstContext_unrollAst(PyObject* self, PyObject* node) {
        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "unrollAst(): Expects a AstNode as argument.");

        try {
          return PyAstNode(triton::ast::unrollAst(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* AstContext_variable(PyObject* self, PyObject* symVar) {
        if (!PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "variable(): expected a SymbolicVariable as first argument");

        try {
          return PyAstNode(PyAstContext_AsAstContext(self)->variable(PySymbolicVariable_AsSymbolicVariable(symVar)));
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

      // *********************************************************************

      #ifdef Z3_INTERFACE
      static PyObject* AstContext_tritonToZ3(PyObject* self, PyObject* node) {
        triton::ast::TritonToZ3Ast tritonToZ3Ast{false};

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "tritonToZ3(): Expects a AstNode as argument.");

        // import z3
        PyObject* z3mod = PyImport_ImportModule("z3");
        if (z3mod == nullptr) {
          return PyErr_Format(PyExc_TypeError, "tritonToZ3(): z3 module not found.");
        }

        // z3.main_ctx().ctx.value
        PyObject* z3MainCtx = PyObject_CallObject(PyObject_GetAttrString(z3mod, "main_ctx"), nullptr);
        PyObject* z3CtxPtr  = PyObject_GetAttrString(PyObject_GetAttrString(z3MainCtx, "ctx"), "value");
        Z3_context z3Ctx    = reinterpret_cast<Z3_context>(PyLong_AsVoidPtr(z3CtxPtr));
        Py_DECREF(z3CtxPtr);
        Py_DECREF(z3MainCtx);

        // Convert the node to a Z3++ expression and translate it into
        // python's z3 main context
        z3::expr expr = tritonToZ3Ast.convert(PyAstNode_AsAstNode(node));
        Z3_ast ast    = Z3_translate(expr.ctx(), expr, z3Ctx);

        // Check that everything went fine
        if (Z3_get_error_code(expr.ctx()) != Z3_OK) {
          Py_DECREF(z3mod);
          return PyErr_Format(PyExc_RuntimeError, "tritonToZ3(): Z3 AST translation failed.");
        }

        // retAst = ctypes.c_void_p(ctx_ptr); retAst.__class__ = z3.Ast
        PyObject* pyArgs = Py_BuildValue("(O)", PyLong_FromVoidPtr(ast));
        PyObject* retAst = PyObject_CallObject(PyObject_GetAttrString(z3mod, "c_void_p"), pyArgs);
        PyObject_SetAttrString(retAst, "__class__", PyObject_GetAttrString(z3mod, "Ast"));
        Py_DECREF(pyArgs);

        // return z3.ExprRef(ast)
        PyObject* z3ExprRef = PyObject_GetAttrString(z3mod, "ExprRef");
        pyArgs = Py_BuildValue("(O)", retAst);
        PyObject* retExpr = PyInstance_New(z3ExprRef, pyArgs, nullptr);
        Py_DECREF(pyArgs);
        Py_DECREF(retAst);
        Py_DECREF(z3ExprRef);

        // Cleanup
        Py_DECREF(z3mod);

        return retExpr;
      }
      #endif


      //! AstContext methods.
      PyMethodDef AstContext_callbacks[] = {
        {"assert_",         AstContext_assert,          METH_O,           ""},
        {"bv",              AstContext_bv,              METH_VARARGS,     ""},
        {"bvadd",           AstContext_bvadd,           METH_VARARGS,     ""},
        {"bvand",           AstContext_bvand,           METH_VARARGS,     ""},
        {"bvashr",          AstContext_bvashr,          METH_VARARGS,     ""},
        {"bvfalse",         AstContext_bvfalse,         METH_NOARGS,      ""},
        {"bvlshr",          AstContext_bvlshr,          METH_VARARGS,     ""},
        {"bvmul",           AstContext_bvmul,           METH_VARARGS,     ""},
        {"bvnand",          AstContext_bvnand,          METH_VARARGS,     ""},
        {"bvneg",           AstContext_bvneg,           METH_O,           ""},
        {"bvnor",           AstContext_bvnor,           METH_VARARGS,     ""},
        {"bvnot",           AstContext_bvnot,           METH_O,           ""},
        {"bvor",            AstContext_bvor,            METH_VARARGS,     ""},
        {"bvrol",           AstContext_bvrol,           METH_VARARGS,     ""},
        {"bvror",           AstContext_bvror,           METH_VARARGS,     ""},
        {"bvsdiv",          AstContext_bvsdiv,          METH_VARARGS,     ""},
        {"bvsge",           AstContext_bvsge,           METH_VARARGS,     ""},
        {"bvsgt",           AstContext_bvsgt,           METH_VARARGS,     ""},
        {"bvshl",           AstContext_bvshl,           METH_VARARGS,     ""},
        {"bvsle",           AstContext_bvsle,           METH_VARARGS,     ""},
        {"bvslt",           AstContext_bvslt,           METH_VARARGS,     ""},
        {"bvsmod",          AstContext_bvsmod,          METH_VARARGS,     ""},
        {"bvsrem",          AstContext_bvsrem,          METH_VARARGS,     ""},
        {"bvsub",           AstContext_bvsub,           METH_VARARGS,     ""},
        {"bvtrue",          AstContext_bvtrue,          METH_NOARGS,      ""},
        {"bvudiv",          AstContext_bvudiv,          METH_VARARGS,     ""},
        {"bvuge",           AstContext_bvuge,           METH_VARARGS,     ""},
        {"bvugt",           AstContext_bvugt,           METH_VARARGS,     ""},
        {"bvule",           AstContext_bvule,           METH_VARARGS,     ""},
        {"bvult",           AstContext_bvult,           METH_VARARGS,     ""},
        {"bvurem",          AstContext_bvurem,          METH_VARARGS,     ""},
        {"bvxnor",          AstContext_bvxnor ,         METH_VARARGS,     ""},
        {"bvxor",           AstContext_bvxor,           METH_VARARGS,     ""},
        {"compound",        AstContext_compound,        METH_O,           ""},
        {"concat",          AstContext_concat,          METH_O,           ""},
        {"declare",         AstContext_declare,         METH_O,           ""},
        {"distinct",        AstContext_distinct,        METH_VARARGS,     ""},
        {"duplicate",       AstContext_duplicate,       METH_O,           ""},
        {"equal",           AstContext_equal,           METH_VARARGS,     ""},
        {"extract",         AstContext_extract,         METH_VARARGS,     ""},
        {"iff",             AstContext_iff,             METH_VARARGS,     ""},
        {"ite",             AstContext_ite,             METH_VARARGS,     ""},
        {"land",            AstContext_land,            METH_O,           ""},
        {"let",             AstContext_let,             METH_VARARGS,     ""},
        {"lnot",            AstContext_lnot,            METH_O,           ""},
        {"lookingForNodes", AstContext_lookingForNodes, METH_VARARGS,     ""},
        {"lor",             AstContext_lor,             METH_O,           ""},
        {"reference",       AstContext_reference,       METH_O,           ""},
        {"string",          AstContext_string,          METH_O,           ""},
        {"sx",              AstContext_sx,              METH_VARARGS,     ""},
        {"unrollAst",       AstContext_unrollAst,       METH_O,           ""},
        {"variable",        AstContext_variable,        METH_O,           ""},
        {"zx",              AstContext_zx,              METH_VARARGS,     ""},
        #ifdef Z3_INTERFACE
        {"tritonToZ3",      AstContext_tritonToZ3,      METH_O,           ""},
        #endif
        {nullptr,           nullptr,                    0,                nullptr}
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
