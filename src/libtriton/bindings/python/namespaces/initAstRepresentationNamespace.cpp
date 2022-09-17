//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/astRepresentation.hpp>



/*! \page py_AST_REPRESENTATION_page AST_REPRESENTATION
    \brief [**python api**] All information about the AST_REPRESENTATION Python namespace.

\tableofcontents

\section AST_REPRESENTATION_py_description Description
<hr>

The AST_REPRESENTATION namespace contains all kinds of AST representations.

\section AST_REPRESENTATION_py_api Python API - Items of the AST_REPRESENTATION namespace
<hr>

- **AST_REPRESENTATION.SMT**<br>
Enabled, AST expressions will be represented in the SMT2-Lib syntax. This is the default mode.

- **AST_REPRESENTATION.PCODE**<br>
Enabled, AST expressions will be represented in a pseudo code syntax.

- **AST_REPRESENTATION.PYTHON**<br>
Enabled, AST expressions will be represented in the Python syntax.

\section AST_REPRESENTATION_py_example_smt Example of SMT representation
<hr>

~~~~~~~~~~~~~{.smt}
>>> ctx.setAstRepresentationMode(AST_REPRESENTATION.SMT)
>>>
>>  inst = Instruction(b"\x48\x31\xd8") # xor rax, rbx
>>> ctx.processing(inst)
>>> for se in inst.getSymbolicExpressions():
...     print(se)
...
(define-fun ref!2 () (_ BitVec 64) (bvxor ref!0 ref!1)) ; XOR operation
(define-fun ref!3 () (_ BitVec 1) (_ bv0 1)) ; Clears carry flag
(define-fun ref!4 () (_ BitVec 1) (_ bv0 1)) ; Clears overflow flag
(define-fun ref!5 () (_ BitVec 1) (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (bvxor (_ bv1 1) ((_ extract 0 0) ref!2)) ((_ extract 1 1) ref!2)) ((_ extract 2 2) ref!2)) ((_ extract 3 3) ref!2)) ((_ extract 4 4) ref!2)) ((_ extract 5 5) ref!2)) ((_ extract 6 6) ref!2)) ((_ extract 7 7) ref!2))) ; Parity flag
(define-fun ref!6 () (_ BitVec 1) ((_ extract 63 63) ref!2)) ; Sign flag
(define-fun ref!7 () (_ BitVec 1) (ite (= ref!2 (_ bv0 64)) (_ bv1 1) (_ bv0 1))) ; Zero flag
(define-fun ref!8 () (_ BitVec 64) (_ bv3 64)) ; Program Counter
~~~~~~~~~~~~~

\section AST_REPRESENTATION_py_example_pcode Example of PCODE representation
<hr>

~~~~~~~~~~~~~{.py}
>>> ctx.setAstRepresentationMode(AST_REPRESENTATION.PCODE)
>>>
>>  inst = Instruction(b"\x48\x31\xd8") # xor rax, rbx
>>> ctx.processing(inst)
>>> for se in inst.getSymbolicExpressions():
...     print(se)
...
rax_2 = (rax_0 ^ rbx_1) ; XOR operation
cf_3 = 0x0 ; Clears carry flag
of_4 = 0x0 ; Clears overflow flag
pf_5 = ((((((((0x1 ^ extract(0, 0, rax_2)) ^ extract(1, 1, rax_2)) ^ extract(2, 2, rax_2)) ^ extract(3, 3, rax_2)) ^ extract(4, 4, rax_2)) ^ extract(5, 5, rax_2)) ^ extract(6, 6, rax_2)) ^ extract(7, 7, rax_2)) ; Parity flag
sf_6 = extract(63, 63, rax_2) ; Sign flag
zf_7 = (0x1 if (rax_2 == 0x0) else 0x0) ; Zero flag
rip_8 = 0x3 ; Program Counter
~~~~~~~~~~~~~

\section AST_REPRESENTATION_py_example_python Example of PYTHON representation
<hr>

~~~~~~~~~~~~~{.py}
>>> ctx.setAstRepresentationMode(AST_REPRESENTATION.SMT)
>>>
>>  inst = Instruction(b"\x48\x31\xd8") # xor rax, rbx
>>> ctx.processing(inst)
>>> for se in inst.getSymbolicExpressions():
...     print(se)
...
ref_2 = (ref_0 ^ ref_1) # XOR operation
ref_3 = 0x0 # Clears carry flag
ref_4 = 0x0 # Clears overflow flag
ref_5 = ((((((((0x1 ^ (ref_2 & 0x1)) ^ ((ref_2 >> 1) & 0x1)) ^ ((ref_2 >> 2) & 0x1)) ^ ((ref_2 >> 3) & 0x1)) ^ ((ref_2 >> 4) & 0x1)) ^ ((ref_2 >> 5) & 0x1)) ^ ((ref_2 >> 6) & 0x1)) ^ ((ref_2 >> 7) & 0x1)) # Parity flag
ref_6 = ((ref_2 >> 63) & 0x1) # Sign flag
ref_7 = (0x1 if (ref_2 == 0x0) else 0x0) # Zero flag
ref_8 = 0x3 # Program Counter
~~~~~~~~~~~~~

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initAstRepresentationNamespace(PyObject* astRepresentationDict) {
        xPyDict_SetItemString(astRepresentationDict, "SMT",    PyLong_FromUint32(triton::ast::representations::SMT_REPRESENTATION));
        xPyDict_SetItemString(astRepresentationDict, "PCODE", PyLong_FromUint32(triton::ast::representations::PCODE_REPRESENTATION));
        xPyDict_SetItemString(astRepresentationDict, "PYTHON", PyLong_FromUint32(triton::ast::representations::PYTHON_REPRESENTATION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
