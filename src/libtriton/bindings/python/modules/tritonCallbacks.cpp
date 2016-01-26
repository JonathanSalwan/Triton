//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <bitsVector.hpp>
#include <cpuSize.hpp>
#include <immediateOperand.hpp>
#include <memoryOperand.hpp>
#include <pythonObjects.hpp>
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>
#include <registerOperand.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_triton_page Python bindings
    \brief [**python api**] All information about the libTriton's Python API.
    \anchor triton

\tableofcontents

\section triton_py_description Description
<hr>

The Triton Triton offers Python bindings on its C++ API which allow you to build analysis in Python as well as in C++.

\section triton_py_api Python API - Classes, methods, modules and namespaces of libTriton
<hr>

By default, the libTriton contains Python bindings and can be loaded with a classical Python `import`.

~~~~~~~~~~~~~{.py}
>>> from triton import *
~~~~~~~~~~~~~

If you want to use the libTriton without Python bindings, recompile the project with the `cmake` flag `-DTRITON_PYTHON_BINDINGS=no`.

\subsection triton_py_api_classes Classes

- \ref py_Bitvector_page
- \ref py_Immediate_page
- \ref py_Instruction_page
- \ref py_Memory_page
- \ref py_Register_page
- \ref py_SmtAstNode_page
- \ref py_SolverModel_page
- \ref py_SymbolicExpression_page
- \ref py_SymbolicVariable_page


\subsection triton_py_api_modules Modules

- \ref smt2lib


\subsection triton_py_api_methods Methods

- <b>assignSymbolicExpressionToRegister(\ref py_SymbolicExpression_page symExpr, \ref py_REG_page reg)</b><br>
Assigns a \ref py_SymbolicExpression_page to a \ref py_REG_page. **Be careful**, use this function only if you know what you are doing.
The symbolic expression (`symExpr`) must be aligned to the targeted size register. E.g: for SSE registers, the expression must be aligned
to 128-bits. Otherwise, you will probably get a sort mismatch error when you will solve the expression. If you want to assign an
expression to a sub-register like `AX`, `AH` or `AL`, please, craft your expression with the `concat()` and `extract()` smt2lib functions.

- **buildSemantics(\ref py_Instruction_page inst)**<br>
Builds the instruction semantics based on the SMT2-Lib representation. You must define an architecture before.

- **concretizeAllMem(void)**<br>
Concretizes all symbolic memory references.

- **concretizeAllReg(void)**<br>
Concretizes all symbolic register references.

- **concretizeMem(integer addr)**<br>
Concretizes a specific symbolic memory reference.

- **concretizeMem(\ref py_Memory_page mem)**<br>
Concretizes a specific symbolic memory reference.

- **concretizeReg(\ref py_REG_page reg)**<br>
Concretizes a specific symbolic register reference.

- **convertExprToSymVar(integer symExprId, integer symVarSize, string comment="")**<br>
Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits. This function returns the \ref py_SymbolicVariable_page created.

- **convertMemToSymVar(\ref py_Memory_page mem, string comment="")**<br>
Converts a symbolic memory expression to a symbolic variable. This function returns the \ref py_SymbolicVariable_page created.

- **convertRegToSymVar(\ref py_REG_page reg, string comment="")**<br>
Converts a symbolic register expression to a symbolic variable. This function returns the \ref py_SymbolicVariable_page created.

- **cpuInvalidReg(void)**<br>
 Returns the invalid CPU register id.

- **cpuNumberOfReg(void)**<br>
Returns the number of registers according to the CPU architecture.

- **cpuRegBitSize(void)**<br>
Returns the max size (in bit) of the CPU register (GPR).

- **cpuRegSize(void)**<br>
Returns the max size (in byte) of the CPU register (GPR).

- <b>createSymbolicFlagExpression(\ref py_Instruction_page inst, \ref py_SmtAstNode_page node, \ref py_REG_page flag, string comment="")</b><br>
Returns the new symbolic register expression as \ref py_SymbolicExpression_page and links this expression to the \ref py_Instruction_page.

- <b>createSymbolicMemoryExpression(\ref py_Instruction_page inst, \ref py_SmtAstNode_page node, \ref py_Memory_page mem, string comment="")</b><br>
Returns the new symbolic memory expression as \ref py_SymbolicExpression_page and links this expression to the \ref py_Instruction_page.

- <b>createSymbolicRegisterExpression(\ref py_Instruction_page inst, \ref py_SmtAstNode_page node, \ref py_REG_page reg, string comment="")</b><br>
Returns the new symbolic register expression as \ref py_SymbolicExpression_page and links this expression to the \ref py_Instruction_page.

- <b>createSymbolicVolatileExpression (\ref py_Instruction_page inst, \ref py_SmtAstNode_page node, string comment="")</b><br>
Returns the new symbolic volatile expression as \ref py_SymbolicExpression_page and links this expression to the \ref py_Instruction_page.

- **disableSymbolicOptimization(\ref py_OPTIMIZATION_page opti)**<br>
Disables the symbolic optimization.

- **disassembly(\ref py_Instruction_page inst)**<br>
Disassembles the instruction and setup operands. You must define an architecture before.

- **enableSymbolicEngine(bool flag)**<br>
Enables or disables the symbolic execution engine.

- **enableSymbolicOptimization(\ref py_OPTIMIZATION_page opti)**<br>
Enables the symbolic optimization.

- **enableTaintEngine(bool flag)**<br>
Enables or disables the taint engine.

- **evaluateAst(\ref py_SmtAstNode_page node)**<br>
Evaluates an AST and returns the symbolic value as integer.

- **getArchitecture(void)**<br>
Returns the architecture which has been initialized as \ref py_ARCH_page.

- **getAstFromId(integer symExprId)**<br>
Returns the partial AST as \ref py_SmtAstNode_page from a symbolic expression id.

- **getAstSummariesStats(void)**<br>
Returns a dictionary which contains all information about number of nodes allocated via AST summaries.

- **getFullAst(\ref py_SmtAstNode_page node)**<br>
Returns the full AST of a root node as \ref py_SmtAstNode_page.

- **getFullAstFromId(integer symExprId)**<br>
Returns the full AST as \ref py_SmtAstNode_page from a symbolic expression id.

- **getLastMemoryValue(intger addr)**<br>
Returns the last concrete value recorded of a memory access.

- **getLastMemoryValue(\ref py_Memory_page mem)**<br>
Returns the last concrete value recorded of a memory access.

- **getLastRegisterValue(\ref py_REG_page reg)**<br>
Returns the last concrete value recorded of a register state.

- **getModel(\ref py_SmtAstNode_page node)**<br>
Computes and returns a model as a dictionary of {integer symVarId : \ref py_SolverModel_page model} from a symbolic constraint.

- **getModels(\ref py_SmtAstNode_page node)**<br>
Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.

- **getParentRegisters(void)**<br>
Returns the list of parent registers. Each item of this list is a \ref py_REG_page.

- **getSymbolicExpressionFromId(intger symExprId)**<br>
Returns the symbolic expression as \ref py_SymbolicExpression_page corresponding to the id.

- **getSymbolicExpressions(void)**<br>
Returns all symbolic expressions as a dictionary of {integer SymExprId : \ref py_SymbolicExpression_page expr}.

- **getSymbolicMemoryId(intger addr)**<br>
Returns the symbolic expression id as integer corresponding to the memory address.

- **getSymbolicRegisterId(\ref py_REG_page reg)**<br>
Returns the symbolic expression id as integer corresponding to the register.

- **getSymbolicVariableFromId(integer symVarId)**<br>
Returns the symbolic variable as \ref py_SymbolicVariable_page corresponding to the symbolic variable id.

- **getSymbolicVariableFromName(string symVarName)**<br>
Returns the symbolic variable as \ref py_SymbolicVariable_page corresponding to the symbolic variable name.

- **getSymbolicVariables(void)**<br>
Returns all symbolic variable as a dictionary of {integer SymVarId : \ref py_SymbolicVariable_page var}.

- **getTaintedSymbolicExpressions(void)**<br>
Returns the list of all tainted \ref py_SymbolicExpression_page.

- **isAddrTainted(integer addr)**<br>
Returns true if the address is tainted.

- **isArchitectureValid(void)**<br>
Returns true if the architecture is valid.

- **isMemTainted(\ref py_Memory_page mem)**<br>
Returns true if the memory is tainted.

- **isRegTainted(\ref py_REG_page reg)**<br>
Returns true if the register is tainted.

- **isSymbolicEngineEnabled(void)**<br>
Returns true if the symbolic execution engine is enabled.

- **isSymbolicExpressionIdExists(integer symExprId)**<br>
Returns true if the symbolic expression id exists.

- **isSymbolicOptimizationEnabled(\ref py_OPTIMIZATION_page opti)**<br>
Returns true if the symbolic optimization is enabled.

- **isTaintEngineEnabled(void)**<br>
Returns true if the taint engine is enabled.

- **newSymbolicExpression(\ref py_SmtAstNode_page node, string comment="")**<br>
Returns a new symbolic expression. Note that if there are simplification passes recorded, simplification will be applied.

- **newSymbolicVariable(intger varSize, string comment="")**<br>
Returns a new symbolic variable.

- **processing(\ref py_Instruction_page inst)**<br>
The main function. This function processes everything (engine, IR, optimization, state, ...) from a given instruction.

- **recordSimplificationCallback(function cb)**<br>
Records a simplification callback. The callback will be called before every symbolic assignments.

- **removeSimplificationCallback(function cb)**<br>
Removes a simplification callback.

- **resetEngines(void)**<br>
Resets everything.

- **setArchitecture(\ref py_ARCH_page arch)**<br>
Initializes an architecture. This function must be called before any call to the rest of the API.

- **setLastMemoryValue(integer addr, integer value)**<br>
Sets the last concrete value of a memory access.

- **setLastMemoryValue(\ref py_Memory_page mem)**<br>
Sets the last concrete value of a memory access.

- **setLastRegisterValue(\ref py_REG_page reg)**<br>
Sets the last concrete value of a register state. You cannot set an isolated flag, if so, use the flags registers like EFLAGS or RFLAGS.

- **setTaintMem(\ref py_Memory_page mem, bool flag)**<br>
Sets the targeted memory as tainted or not.

- **setTaintReg(\ref py_REG_page reg, bool flag)**<br>
Sets the targeted register as tainted or not.

- **simplify(\ref py_SmtAstNode_page node)**<br>
Calls all simplification callbacks recorded and returns the simplified node as \ref py_SmtAstNode_page.

- **taintAddr(intger addr)**<br>
Taints an address.

- <b>taintAssignmentMemImm(\ref py_Memory_page memDst)</b><br>
Taints `memDst` with an assignment - `memDst` is untained.

- <b>taintAssignmentMemMem(\ref py_Memory_page memDst, \ref py_Memory_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an assignment - `memDst` is tainted if `memSrc` is tainted, otherwise `memDst` is untained.

- <b>taintAssignmentMemReg(\ref py_Memory_page memDst, \ref py_REG_page regSrc)</b><br>
Taints `memDst` from `regSrc` with an assignment - `memDst` is tainted if `regSrc` is tainted, otherwise `memDst` is untained.

- <b>taintAssignmentRegImm(\ref py_REG_page regDst)</b><br>
Taints `regDst` with an assignment - `regSrc` is untained.

- <b>taintAssignmentRegMem(\ref py_REG_page regDst, \ref py_Memory_page memSrc)</b><br>
Taints `regDst` from `MemSrc` with an assignment - `regDst` is tainted if `memSrc` is tainted, otherwise `regDst` is untained.

- <b>taintAssignmentRegReg(\ref py_REG_page regDst, \ref py_REG_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an assignment - `regDst` is tainted if `regSrc` is tainted, otherwise `regDst` is untained.

- **taintMem(\ref py_Memory_page mem)**<br>
Taints a memory.

- **taintReg(\ref py_REG_page reg)**<br>
Taints a register.

- <b>taintUnionMemImm(\ref py_Memory_page memDst)</b><br>
Taints `memDst` with an union - `memDst` does not changes.

- <b>taintUnionMemMem(\ref py_Memory_page memDst, \ref py_Memory_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an union - `memDst` is tainted if `memDst` or `memSrc` are tainted.

- <b>taintUnionMemReg(\ref py_Memory_page memDst, \ref py_REG_page regSrc)</b><br>
Taints `memDst` from `RegSrc` with an union - `memDst` is tainted if `memDst` or `regSrc` are tainted.

- <b>taintUnionRegImm(\ref py_REG_page regDst)</b><br>
Taints `regDst` with an union - `regDst` does not changes.

- <b>taintUnionRegMem(\ref py_REG_page regDst, \ref py_Memory_page memSrc)</b><br>
Taints `regDst` from `memSrc` with an union - `regDst` is tainted if `regDst` or `memSrc` are tainted.

- <b>taintUnionRegReg(\ref py_REG_page regDst, \ref py_REG_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an union - `regDst` is tainted if `regDst` or `regSrc` are tainted.

- **untaintAddr(intger addr)**<br>
Untaints an address.

- **untaintMem(\ref py_Memory_page mem)**<br>
Untaints a memory.

- **untaintReg(\ref py_REG_page reg)**<br>
Untaints a register.


\subsection triton_py_api_namespaces Namespaces

- \ref py_ARCH_page
- \ref py_CPUSIZE_page
- \ref py_OPCODE_page
- \ref py_OPERAND_page
- \ref py_OPTIMIZATION_page
- \ref py_REG_page
- \ref py_SMT_AST_NODE_page
- \ref py_SYMEXPR_page
- \ref py_SYSCALL_page
- \ref py_VERSION_page

\section pintool_py_api Python API - Methods and namespaces of the pintool
<hr>

This project is shipped with a Pin \ref Tracer_page which can be compile with the `cmake` flag `-DPINTOOL=yes`. Then, the pintool must be used like this:


~~~~~~~~~~~~~{.sh}
$ ./triton <your_script.py> <your_targeted_binary>
~~~~~~~~~~~~~

Your script must contains the pintool and triton imports.

~~~~~~~~~~~~~{.py}
>>> from triton import *
>>> from pintool import *
~~~~~~~~~~~~~


\subsection pintool_py_api_methods Methods

- <b>addCallback(function, \ref py_CALLBACK_page type)</b><br>
Adds a callback before and after several cases. All code executed into a callback function are executed during the instrumentation.

- **checkReadAccess(integer addr)**<br>
Checks whether the memory page which contains this address has a read access protection. Returns true or false.

- **checkWriteAccess(integer addr)**<br>
Checks whether the memory page which contains this address has a write access protection. Returns true or false.

- **detachProcess(void)**<br>
Detachs the pintool from the targeted process. The control flow is returned to the original uninstrumented code and the application is natively executed.

- **disableSnapshot(void)**<br>
Disables the snapshot engine. When you have done with the `tracer::pintool::Snapshot::restoreSnapshot()` function, you may use this function to improve performance. Then, the
snapshot engine will be enable at the next `tracer::pintool::Snapshot::takeSnapshot()` call.

- **getCurrentMemoryValue(\ref py_Memory_page mem)**<br>
Returns the memory value from a \ref py_Memory_page.

- **getCurrentMemoryValue(integer addr)**<br>
Returns the memory value from the address.

- **getCurrentMemoryValue(integer addr, integer readSize)**<br>
Returns the memory value according to the `readSize` from the address.

- **getCurrentRegisterValue(\ref py_REG_page reg)**<br>
Returns the register value from a \ref py_REG_page.

- **getImageName(integer addr)**<br>
Returns the image name from a given address. Returns an empty string if not found.

- **getRoutineName(integer addr)**<br>
Returns the routine name from a given address. Returns an empty string if not found.

- **getSyscallArgument(\ref py_STANDARD_page std, integer argNum)**<br>
Returns the argument's value of the system call which is executed in the current context. It is a user's responsibility to make sure that the
current instruction is a syscall. This function is mainly used in a `SYSCALL_ENTRY` \ref py_CALLBACK_page.

- **getSyscallNumber(\ref py_STANDARD_page std)**<br>
Returns the syscall's number of the system call which is executed in the current context. It is a user's responsibility to make sure that the
current instruction is a syscall. This function is mainly used in a `SYSCALL_ENTRY` \ref py_CALLBACK_page.

- **getSyscallReturn(\ref py_STANDARD_page std)**<br>
Returns the syscall's result. It is a user's responsibility to make sure that the current context represents the state of a system call after its execution.
This function is mainly used in a `SYSCALL_EXIT` \ref py_CALLBACK_page.

- **isSnapshotEnabled(void)**<br>
Returns true if the snapshot engine is enabled.

- **restoreSnapshot(void)**<br>
Restores the last snpahost taken. Check the `tracer::pintool::Snapshot::takeSnapshot()` function. Note that this function have to execute a new context registers, so `RIP` will be modified and your callback stopped (checkout the [Pin API](https://software.intel.com/sites/landingpage/pintool/docs/71313/Pin/html/group__CONTEXT__API.html#g4e6408c641479c22918a888d95ca1930)).

- **runProgram(void)**<br>
Starts the binary instrumentation over Pin.

- **setCurrentMemoryValue(\ref py_Memory_page mem)**<br>
Sets the current memory value from a \ref py_Memory_page. `triton::arch::MemoryOperand::getConcreteValue()` is used to define the value.

- **setCurrentMemoryValue(\ref py_Memory_page mem, integer value)**<br>
Sets the current memory value from a \ref py_Memory_page.

- **setCurrentMemoryValue(integer addr, integer value)**<br>
Sets the current memory value from an address.

- **setCurrentRegisterValue(\ref py_Register_page reg)**<br>
Sets the current register value from a \ref py_Register_page. `triton::arch::RegisterOperand::getConcreteValue()` is used to define the value. This method can only be called into a `BEFORE_SYMPROC` and `AFTER` callback. This method also synchronizes the Triton's register.

- **setCurrentRegisterValue(\ref py_Register_page reg, integer value)**<br>
Sets the current register value from a \ref py_Register_page. This method can only be called into a `BEFORE_SYMPROC` and `AFTER` callback. This method also synchronizes the Triton's register.

- **setupImageBlacklist([""])**<br>
Setups a blacklist of image names, it means that these images will not be instrumented and executed natively.

- **setupImageWhitelist([""])**<br>
Setups a whitelist of image names, it means that these images will be instrumented and all other images will be executed natively.

- **startAnalysisFromAddr(integer addr)**<br>
Starts the instrumentation at a specific address.

- **startAnalysisFromEntry(void)**<br>
Starts the instrumentation at the entry point.

- **startAnalysisFromOffset(integer offset)**<br>
Starts the instrumentation at a specific offset in the binary

- **startAnalysisFromSymbol(string symbol)**<br>
Starts the instrumentation at a specific symbol.

- **stopAnalysisFromAddr(integer addr)**<br>
Stops the instrumentation at a specific address.

- **stopAnalysisFromOffset(integer offset)**<br>
Stops the instrumentation at a specific offset.

- **takeSnapshot(void)**<br>
Creates a snaphost at this program point.

\subsection pintool_py_api_namespaces Namespaces

- \ref py_CALLBACK_page
- \ref py_STANDARD_page

*/



namespace triton {
  namespace bindings {
    namespace python {

      static PyObject* triton_Bitvector(PyObject* self, PyObject* args) {
        PyObject* high = nullptr;
        PyObject* low  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &high, &low);

        /* Check if the first arg is a integer */
        if (high == nullptr || (!PyLong_Check(high) && !PyInt_Check(high)))
          return PyErr_Format(PyExc_TypeError, "Bitvector(): Expects an integer as first argument.");

        /* Check if the second arg is a integer */
        if (low == nullptr || (!PyLong_Check(low) && !PyInt_Check(low)))
          return PyErr_Format(PyExc_TypeError, "Bitvector(): Expects an integer as second argument.");

        try {
          return PyBitvector(PyLong_AsUint(high), PyLong_AsUint(low));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_Immediate(PyObject* self, PyObject* args) {
        PyObject* value = nullptr;
        PyObject* size  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &value, &size);

        /* Check if the first arg is a integer */
        if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
          return PyErr_Format(PyExc_TypeError, "Immediate(): Expects an integer as first argument.");

        /* Check if the second arg is a integer */
        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "Immediate(): Expects an integer as second argument.");

        try {
          triton::arch::ImmediateOperand imm(PyLong_AsUint(value), PyLong_AsUint(size));
          return PyImmediateOperand(imm);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_Instruction(PyObject* self, PyObject* noarg) {
        return PyInstruction();
      }


      static PyObject* triton_Memory(PyObject* self, PyObject* args) {
        PyObject* address       = nullptr;
        PyObject* size          = nullptr;
        PyObject* concreteValue = nullptr;
        triton::uint128 cv      = 0;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &address, &size, &concreteValue);

        /* Check if the first arg is a integer */
        if (address == nullptr || (!PyLong_Check(address) && !PyInt_Check(address)))
          return PyErr_Format(PyExc_TypeError, "Memory(): Expects an integer as first argument.");

        /* Check if the second arg is a integer */
        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "Memory(): Expects an integer as second argument.");

        /* Check if the third arg is a integer */
        if (concreteValue != nullptr && (!PyLong_Check(concreteValue) && !PyInt_Check(concreteValue)))
          return PyErr_Format(PyExc_TypeError, "Memory(): Expects an integer as third argument.");

        if (concreteValue != nullptr)
          cv = PyLong_AsUint128(concreteValue);

        try {
          triton::arch::MemoryOperand mem(PyLong_AsUint(address), PyLong_AsUint(size), cv);
          return PyMemoryOperand(mem);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_Register(PyObject* self, PyObject* args) {
        PyObject* concreteValue         = nullptr;
        PyObject* regIn                 = nullptr;
        triton::uint128 cv              = 0;
        triton::arch::RegisterOperand*  r;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &regIn, &concreteValue);

        /* Check if the first arg is a Register */
        if (regIn == nullptr || !PyRegisterOperand_Check(regIn))
          return PyErr_Format(PyExc_TypeError, "Register(): Expects a Register as first argument.");

        /* Check if the second arg is a integer */
        if (concreteValue != nullptr && (!PyLong_Check(concreteValue) && !PyInt_Check(concreteValue)))
          return PyErr_Format(PyExc_TypeError, "Register(): Expects an integer as second argument.");

        if (concreteValue != nullptr)
          cv = PyLong_AsUint128(concreteValue);

        try {
          r = PyRegisterOperand_AsRegisterOperand(regIn);
          triton::arch::RegisterOperand regOut(r->getId(), cv);
          return PyRegisterOperand(regOut);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_assignSymbolicExpressionToRegister(PyObject* self, PyObject* args) {
        PyObject* se  = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &se, &reg);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Architecture is not defined.");

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a SymbolicExpression as first argument.");

        if (reg == nullptr || (!PyRegisterOperand_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a REG as second argument.");

        triton::engines::symbolic::SymbolicExpression* arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::RegisterOperand arg2 = *PyRegisterOperand_AsRegisterOperand(reg);

        try {
          triton::api.assignSymbolicExpressionToRegister(arg1, arg2);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_buildSemantics(PyObject* self, PyObject* inst) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSemantics(): Architecture is not defined.");

        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "buildSemantics(): Expects an Instruction as argument.");

        try {
          triton::api.buildSemantics(*PyInstruction_AsInstruction(inst));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeAllMem(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeAllMem(): Architecture is not defined.");
        triton::api.concretizeAllMem();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeAllReg(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeAllReg(): Architecture is not defined.");
        triton::api.concretizeAllReg();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeMem(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeMem(): Architecture is not defined.");

        /* If mem is an address */
        if (PyLong_Check(mem) || PyInt_Check(mem)) {
          try {
            triton::api.concretizeMem(PyLong_AsUint(mem));
          }
          catch (const std::exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* If mem is a Memory */
        else if (PyMemoryOperand_Check(mem)) {
          try {
            triton::api.concretizeMem(*PyMemoryOperand_AsMemoryOperand(mem));
          }
          catch (const std::exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* Invalid parameter */
        else
          return PyErr_Format(PyExc_TypeError, "concretizeMem(): Expects an integer or Memory as argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeReg(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeReg(): Architecture is not defined.");

        /* If mem is a Memory */
        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "concretizeReg(): Expects a REG as argument.");

        try {
          triton::api.concretizeReg(*PyRegisterOperand_AsRegisterOperand(reg));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_convertExprToSymVar(PyObject* self, PyObject* args) {
        PyObject* exprId        = nullptr;
        PyObject* symVarSize    = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &exprId, &symVarSize, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): Architecture is not defined.");

        if (exprId == nullptr || (!PyLong_Check(exprId) && !PyInt_Check(exprId)))
          return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): Expects an integer as first argument.");

        if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
          return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): Expects an integer as second argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertExprToSymVar(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.convertExprToSymVar(PyLong_AsUint(exprId), PyLong_AsUint(symVarSize), ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_convertMemToSymVar(PyObject* self, PyObject* args) {
        PyObject* mem           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): Architecture is not defined.");

        if (mem == nullptr || (!PyMemoryOperand_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): Expects a Memory as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertMemToSymVar(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.convertMemToSymVar(*PyMemoryOperand_AsMemoryOperand(mem), ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_convertRegToSymVar(PyObject* self, PyObject* args) {
        PyObject* reg           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): Architecture is not defined.");

        if (reg == nullptr || (!PyRegisterOperand_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): Expects a REG as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertRegToSymVar(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.convertRegToSymVar(*PyRegisterOperand_AsRegisterOperand(reg), ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_cpuInvalidReg(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", triton::api.cpuInvalidReg());
      }


      static PyObject* triton_cpuNumberOfReg(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", triton::api.cpuNumberOfReg());
      }


      static PyObject* triton_cpuRegBitSize(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", triton::api.cpuRegBitSize());
      }


      static PyObject* triton_cpuRegSize(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", triton::api.cpuRegSize());
      }


      static PyObject* triton_createSymbolicFlagExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* flag          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOOO", &inst, &node, &flag, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PySmtAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a SmtAstNode as second argument.");

        if (flag == nullptr || (!PyRegisterOperand_Check(flag)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a REG as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::smt2lib::smtAstAbstractNode *arg2 = PySmtAstNode_AsSmtAstNode(node);
        triton::arch::RegisterOperand arg3 = *PyRegisterOperand_AsRegisterOperand(flag);

        try {
          return PySymbolicExpression(triton::api.createSymbolicFlagExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_createSymbolicMemoryExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* mem           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOOO", &inst, &node, &mem, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PySmtAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects a SmtAstNode as second argument.");

        if (mem == nullptr || (!PyMemoryOperand_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects a Memory as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::smt2lib::smtAstAbstractNode *arg2 = PySmtAstNode_AsSmtAstNode(node);
        triton::arch::MemoryOperand arg3 = *PyMemoryOperand_AsMemoryOperand(mem);

        try {
          return PySymbolicExpression(triton::api.createSymbolicMemoryExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_createSymbolicRegisterExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* reg           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOOO", &inst, &node, &reg, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PySmtAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a SmtAstNode as second argument.");

        if (reg == nullptr || (!PyRegisterOperand_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a REG as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::smt2lib::smtAstAbstractNode *arg2 = PySmtAstNode_AsSmtAstNode(node);
        triton::arch::RegisterOperand arg3 = *PyRegisterOperand_AsRegisterOperand(reg);

        try {
          return PySymbolicExpression(triton::api.createSymbolicRegisterExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_createSymbolicVolatileExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &inst, &node, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PySmtAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects a SmtAstNode as second argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::smt2lib::smtAstAbstractNode *arg2 = PySmtAstNode_AsSmtAstNode(node);

        try {
          return PySymbolicExpression(triton::api.createSymbolicVolatileExpression(arg1, arg2, ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_disableSymbolicOptimization(PyObject* self, PyObject* opti) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "disableSymbolicOptimization(): Architecture is not defined.");

        if (!PyLong_Check(opti) && !PyInt_Check(opti))
          return PyErr_Format(PyExc_TypeError, "disableSymbolicOptimization(): Expects an OPTIMIZATION as argument.");

        try {
          triton::api.disableSymbolicOptimization(static_cast<enum triton::engines::symbolic::optimization_e>(PyLong_AsUint(opti)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_disassembly(PyObject* self, PyObject* inst) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "disassembly(): Architecture is not defined.");

        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "disassembly(): Expects an Instruction as argument.");

        try {
          triton::api.disassembly(*PyInstruction_AsInstruction(inst));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_enableSymbolicEngine(PyObject* self, PyObject* flag) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableSymbolicEngine(): Architecture is not defined.");

        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "enableSymbolicEngine(): Expects an boolean as argument.");

        try {
          triton::api.enableSymbolicEngine(PyLong_AsUint(flag));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_enableSymbolicOptimization(PyObject* self, PyObject* opti) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableSymbolicOptimization(): Architecture is not defined.");

        if (!PyLong_Check(opti) && !PyInt_Check(opti))
          return PyErr_Format(PyExc_TypeError, "enableSymbolicOptimization(): Expects an OPTIMIZATION as argument.");

        try {
          triton::api.enableSymbolicOptimization(static_cast<enum triton::engines::symbolic::optimization_e>(PyLong_AsUint(opti)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_enableTaintEngine(PyObject* self, PyObject* flag) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableTaintEngine(): Architecture is not defined.");

        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "enableTaintEngine(): Expects an boolean as argument.");

        try {
          triton::api.enableTaintEngine(PyLong_AsUint(flag));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_evaluateAst(PyObject* self, PyObject* node) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "evaluateAst(): Architecture is not defined.");

        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "evaluateAst(): Expects a SmtAstNode as argument.");

        try {
          return PyLong_FromUint512(triton::api.evaluateAst(PySmtAstNode_AsSmtAstNode(node)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        catch (const z3::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.msg());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_getArchitecture(PyObject* self, PyObject* noarg) {
        return Py_BuildValue("k", triton::api.getArchitecture());
      }


      static PyObject* triton_getAstFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getAstFromId(): Expects an integer as argument.");

        try {
          return PySmtAstNode(triton::api.getAstFromId(PyLong_AsUint(symExprId)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getAstSummariesStats(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        std::map<std::string, triton::uint32> stats;
        std::map<std::string, triton::uint32>::iterator it;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstSummariesStats(): Architecture is not defined.");

        try {
          stats = triton::api.getAstSummariesStats();
          ret   = xPyDict_New();
          for (it = stats.begin(); it != stats.end(); it++)
            PyDict_SetItem(ret, PyString_FromString(it->first.c_str()), PyLong_FromUint(it->second));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getFullAst(PyObject* self, PyObject* node) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getFullAst(): Architecture is not defined.");

        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getFullAst(): Expects a SmtAstNode as argument.");

        try {
          return PySmtAstNode(triton::api.getFullAst(PySmtAstNode_AsSmtAstNode(node)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getFullAstFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getFullAstFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getFullAstFromId(): Expects an integer as argument.");

        try {
          return PySmtAstNode(triton::api.getFullAstFromId(PyLong_AsUint(symExprId)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getLastMemoryValue(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getLastMemoryValue(): Architecture is not defined.");

        if (PyLong_Check(mem) || PyInt_Check(mem)) {
          try {
            return PyLong_FromUint128(triton::api.getLastMemoryValue(PyLong_AsUint(mem)));
          }
          catch (const std::exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        else if (PyMemoryOperand_Check(mem)) {
          try {
            return PyLong_FromUint128(triton::api.getLastMemoryValue(*PyMemoryOperand_AsMemoryOperand(mem)));
          }
          catch (const std::exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        else
          return PyErr_Format(PyExc_TypeError, "getLastMemoryValue(): Expects a Memory or an integer as argument.");
      }


      static PyObject* triton_getLastRegisterValue(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getLastRegisterValue(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getLastRegisterValue(): Expects a REG as argument.");

        try {
          return PyLong_FromUint128(triton::api.getLastRegisterValue(*PyRegisterOperand_AsRegisterOperand(reg)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getModel(PyObject* self, PyObject* node) {
        PyObject* ret = nullptr;
        std::map<triton::uint32, triton::engines::solver::SolverModel> model;
        std::map<triton::uint32, triton::engines::solver::SolverModel>::iterator it;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getModel(): Architecture is not defined.");

        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModel(): Expects a SmtAstNode as argument.");

        try {
          ret = xPyDict_New();
          model = triton::api.getModel(PySmtAstNode_AsSmtAstNode(node));
          for (it = model.begin(); it != model.end(); it++) {
            PyDict_SetItem(ret, PyLong_FromUint(it->first), PySolverModel(it->second));
          }
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getModels(PyObject* self, PyObject* args) {
        PyObject* ret   = nullptr;
        PyObject* node  = nullptr;
        PyObject* limit = nullptr;
        triton::uint32 index = 0;
        std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>> models;
        std::list<std::map<triton::uint32, triton::engines::solver::SolverModel>>::iterator it;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &limit);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getModels(): Architecture is not defined.");

        if (node == nullptr || !PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModels(): Expects a SmtAstNode as first argument.");

        if (limit == nullptr || (!PyLong_Check(limit) && !PyInt_Check(limit)))
          return PyErr_Format(PyExc_TypeError, "getModels(): Expects an integer as second argument.");

        try {
          models = triton::api.getModels(PySmtAstNode_AsSmtAstNode(node), PyLong_AsUint(limit));
          ret = xPyList_New(models.size());
          for (it = models.begin(); it != models.end(); it++) {
            PyObject* mdict = xPyDict_New();
            std::map<triton::uint32, triton::engines::solver::SolverModel> model = *it;
            for (auto it2 = model.begin(); it2 != model.end(); it2++) {
              PyDict_SetItem(mdict, PyLong_FromUint(it2->first), PySolverModel(it2->second));
            }
            if (model.size() > 0)
              PyList_SetItem(ret, index++, mdict);
          }
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getParentRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        std::set<triton::arch::RegisterOperand*> reg;
        std::set<triton::arch::RegisterOperand*>::iterator it;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getParentRegisters(): Architecture is not defined.");

        try {
          reg = triton::api.getParentRegisters();
          ret = xPyList_New(reg.size());
          triton::uint32 index = 0;
          for (it = reg.begin(); it != reg.end(); it++)
            PyList_SetItem(ret, index++, PyRegisterOperand(**it));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getSymbolicExpressionFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicExpressionFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getSymbolicExpressionFromId(): Expects an integer as argument.");

        try {
          return PySymbolicExpression(triton::api.getSymbolicExpressionFromId(PyLong_AsUint(symExprId)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicExpressions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*>& expressions = triton::api.getSymbolicExpressions();
        std::map<triton::__uint, triton::engines::symbolic::SymbolicExpression*>::iterator it;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicExpressions(): Architecture is not defined.");

        try {
          ret = xPyDict_New();
          for (it = expressions.begin(); it != expressions.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUint(it->first), PySymbolicExpression(it->second));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getSymbolicMemoryId(PyObject* self, PyObject* addr) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryId(): Architecture is not defined.");

        if (!PyLong_Check(addr) && !PyInt_Check(addr))
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryId(): Expects an integer as argument.");

        try {
          return PyLong_FromUint(triton::api.getSymbolicMemoryId(PyLong_AsUint(addr)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicRegisterId(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterId(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterId(): Expects a REG as argument.");

        try {
          return PyLong_FromUint(triton::api.getSymbolicRegisterId(*PyRegisterOperand_AsRegisterOperand(reg)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicVariableFromId(PyObject* self, PyObject* symVarId) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromId(): Architecture is not defined.");

        if (!PyLong_Check(symVarId) && !PyInt_Check(symVarId))
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromId(): Expects an integer as argument.");

        try {
          return PySymbolicVariable(triton::api.getSymbolicVariableFromId(PyLong_AsUint(symVarId)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicVariableFromName(PyObject* self, PyObject* symVarName) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromName(): Architecture is not defined.");

        if (!PyString_Check(symVarName))
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromName(): Expects a string as argument.");

        try {
          std::string arg = PyString_AsString(symVarName);
          return PySymbolicVariable(triton::api.getSymbolicVariableFromName(arg));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicVariables(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        std::map<triton::__uint, triton::engines::symbolic::SymbolicVariable*>& variables = triton::api.getSymbolicVariables();
        std::map<triton::__uint, triton::engines::symbolic::SymbolicVariable*>::iterator it;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicVariables(): Architecture is not defined.");

        try {
          ret = xPyDict_New();
          for (it = variables.begin(); it != variables.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUint(it->first), PySymbolicVariable(it->second));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getTaintedSymbolicExpressions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::uint32 size = 0, index = 0;
        std::list<triton::engines::symbolic::SymbolicExpression*> expressions;
        std::list<triton::engines::symbolic::SymbolicExpression*>::iterator it;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicExpressions(): Architecture is not defined.");

        try {
          expressions = triton::api.getTaintedSymbolicExpressions();
          size = expressions.size();
          ret = xPyList_New(size);
          for (it = expressions.begin(); it != expressions.end(); it++) {
            PyList_SetItem(ret, index, PySymbolicExpression(*it));
            index++;
          }
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_isAddrTainted(PyObject* self, PyObject* addr) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isAddrTainted(): Architecture is not defined.");

        if (!PyLong_Check(addr) && !PyInt_Check(addr))
          return PyErr_Format(PyExc_TypeError, "isAddrTainted(): Expects an integer as argument.");

        if (triton::api.isAddrTainted(PyLong_AsUint(addr)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isArchitectureValid(PyObject* self, PyObject* noarg) {
        if (triton::api.isArchitectureValid() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isMemTainted(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemTainted(): Architecture is not defined.");

        if (!PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "isMemTainted(): Expects a Memory as argument.");

        if (triton::api.isMemTainted(*PyMemoryOperand_AsMemoryOperand(mem)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isRegTainted(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegTainted(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegTainted(): Expects a REG as argument.");

        if (triton::api.isRegTainted(*PyRegisterOperand_AsRegisterOperand(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isSymbolicEngineEnabled(PyObject* self, PyObject* noarg) {
        if (triton::api.isSymbolicEngineEnabled() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isSymbolicExpressionIdExists(PyObject* self, PyObject* symExprId) {
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Architecture is not defined.");

        if (!PyInt_Check(symExprId) && !PyLong_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Expects an integer as argument.");

        if (triton::api.isSymbolicExpressionIdExists(PyLong_AsUint(symExprId)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isSymbolicOptimizationEnabled(PyObject* self, PyObject* opti) {
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isSymbolicOptimizationEnabled(): Architecture is not defined.");

        if (!PyInt_Check(opti) && !PyLong_Check(opti))
          return PyErr_Format(PyExc_TypeError, "isSymbolicOptimizationEnabled(): Expects an OPTIMIZATION as argument.");

        if (triton::api.isSymbolicOptimizationEnabled(static_cast<enum triton::engines::symbolic::optimization_e>(PyLong_AsUint(opti))) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isTaintEngineEnabled(PyObject* self, PyObject* noarg) {
        if (triton::api.isTaintEngineEnabled() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_newSymbolicExpression(PyObject* self, PyObject* args) {
        PyObject* node          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Architecture is not defined.");

        if (node == nullptr || (!PySmtAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Expects a SmtAstNode as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicExpression(triton::api.newSymbolicExpression(PySmtAstNode_AsSmtAstNode(node), ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_newSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* size        = nullptr;
        PyObject* comment     = nullptr;
        std::string ccomment  = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &size, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "newSymbolicVariable(): Architecture is not defined.");

        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "newSymbolicVariable(): Expects an integer as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "newSymbolicVariable(): Expects a sting as second  argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.newSymbolicVariable(PyLong_AsUint(size), ccomment));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_processing(PyObject* self, PyObject* inst) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "processing(): Architecture is not defined.");

        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "processing(): Expects an Instruction as argument.");

        try {
          triton::api.processing(*PyInstruction_AsInstruction(inst));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_recordSimplificationCallback(PyObject* self, PyObject* cb) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "recordSimplificationCallback(): Architecture is not defined.");

        if (!PyCallable_Check(cb))
          return PyErr_Format(PyExc_TypeError, "recordSimplificationCallback(): Expects a callback function as argument.");

        try {
          triton::api.recordSimplificationCallback(cb);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_removeSimplificationCallback(PyObject* self, PyObject* cb) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "removeSimplificationCallback(): Architecture is not defined.");

        if (!PyCallable_Check(cb))
          return PyErr_Format(PyExc_TypeError, "removeSimplificationCallback(): Expects a callback function as argument.");

        try {
          triton::api.removeSimplificationCallback(cb);
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_resetEngines(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "resetEngines(): Architecture is not defined.");

        try {
          triton::api.resetEngines();
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setArchitecture(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "setArchitecture(): Expects an ARCH as argument.");

        try {
          triton::api.setArchitecture(PyLong_AsUint(arg));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setLastMemoryValue(PyObject* self, PyObject* args) {
        PyObject* mem    = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &value);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setLastMemoryValue(): Architecture is not defined.");

        /* setLastMemoryValue(integer, integer) */
        if (mem != nullptr && (PyLong_Check(mem) || PyInt_Check(mem))) {
          if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
            return PyErr_Format(PyExc_TypeError, "setLastMemoryValue(): Expects a value as second argument.");

          triton::__uint addr = PyLong_AsUint(mem);
          triton::__uint cvalue = PyLong_AsUint(value);

          if (cvalue > 0xff)
            return PyErr_Format(PyExc_TypeError, "setLastMemoryValue(): Value must be on 8 bits.");

          try {
            triton::api.setLastMemoryValue(addr, cvalue);
          }
          catch (const std::exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }

        }

        /* setLastMemoryValue(MemoryOperand) */
        else if (mem != nullptr && PyMemoryOperand_Check(mem)) {
          if (value != nullptr)
            return PyErr_Format(PyExc_TypeError, "setLastMemoryValue(): Expects no second argument.");
          try {
            triton::api.setLastMemoryValue(*PyMemoryOperand_AsMemoryOperand(mem));
          }
          catch (const std::exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* Invalid */
        else
          return PyErr_Format(PyExc_TypeError, "setLastMemoryValue(): Expects a Memory or an integer as first argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setLastRegisterValue(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setLastRegisterValue(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "setLastRegisterValue(): Expects a REG as first argument.");

        try {
          triton::api.setLastRegisterValue(*PyRegisterOperand_AsRegisterOperand(reg));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setTaintMem(PyObject* self, PyObject* args) {
        PyObject* mem    = nullptr;
        PyObject* flag   = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &flag);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setTaintMem(): Architecture is not defined.");

        if (mem == nullptr || !PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "setTaintMem(): Expects a Memory as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTaintMem(): Expects a boolean as second argument.");

        try {
          if (triton::api.setTaintMem(*PyMemoryOperand_AsMemoryOperand(mem), PyLong_AsUint(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_setTaintReg(PyObject* self, PyObject* args) {
        PyObject* reg    = nullptr;
        PyObject* flag   = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &flag);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setTaintReg(): Architecture is not defined.");

        if (reg == nullptr || !PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "setTaintReg(): Expects a REG as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTaintReg(): Expects a boolean as second argument.");

        try {
          if (triton::api.setTaintReg(*PyRegisterOperand_AsRegisterOperand(reg), PyLong_AsUint(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_simplify(PyObject* self, PyObject* node) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "simplify(): Architecture is not defined.");

        if (!PySmtAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "simplify(): Expects a SmtAstNode as argument.");

        try {
          return PySmtAstNode(triton::api.processSimplification(PySmtAstNode_AsSmtAstNode(node)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAddr(PyObject* self, PyObject* addr) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAddr(): Architecture is not defined.");

        if (!PyLong_Check(addr) && !PyInt_Check(addr))
          return PyErr_Format(PyExc_TypeError, "taintAddr(): Expects an intger as argument.");

        try {
          if (triton::api.taintAddr(PyLong_AsUint(addr)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentMemImm(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemImm(): Architecture is not defined.");

        if (!PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemImm(): Expects a Memory as argument.");

        try {
          if (triton::api.taintAssignmentMemImm(*PyMemoryOperand_AsMemoryOperand(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentMemMem(PyObject* self, PyObject* args) {
        PyObject* mem1 = nullptr;
        PyObject* mem2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem1, &mem2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemMem(): Architecture is not defined.");

        if (mem1 == nullptr || !PyMemoryOperand_Check(mem1))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemMem(): Expects a Memory as first argument.");

        if (mem2 == nullptr || !PyMemoryOperand_Check(mem2))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemMem(): Expects a Memory as second argument.");

        try {
          if (triton::api.taintAssignmentMemMem(*PyMemoryOperand_AsMemoryOperand(mem1), *PyMemoryOperand_AsMemoryOperand(mem2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentMemReg(PyObject* self, PyObject* args) {
        PyObject* mem = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &reg);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemReg(): Architecture is not defined.");

        if (mem == nullptr || !PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemReg(): Expects a Memory as first argument.");

        if (reg == nullptr || !PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemReg(): Expects a REG as second argument.");

        try {
          if (triton::api.taintAssignmentMemReg(*PyMemoryOperand_AsMemoryOperand(mem), *PyRegisterOperand_AsRegisterOperand(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentRegImm(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegImm(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegImm(): Expects a REG as argument.");

        try {
          if (triton::api.taintAssignmentRegImm(*PyRegisterOperand_AsRegisterOperand(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentRegMem(PyObject* self, PyObject* args) {
        PyObject* reg = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &mem);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegMem(): Architecture is not defined.");

        if (reg == nullptr || !PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegMem(): Expects a REG as first argument.");

        if (mem == nullptr || !PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegMem(): Expects a Memory as second argument.");

        try {
          if (triton::api.taintAssignmentRegMem(*PyRegisterOperand_AsRegisterOperand(reg), *PyMemoryOperand_AsMemoryOperand(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentRegReg(PyObject* self, PyObject* args) {
        PyObject* reg1 = nullptr;
        PyObject* reg2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg1, &reg2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegReg(): Architecture is not defined.");

        if (reg1 == nullptr || !PyRegisterOperand_Check(reg1))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegReg(): Expects a REG as first argument.");

        if (reg2 == nullptr || !PyRegisterOperand_Check(reg2))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegReg(): Expects a REG as second argument.");

        try {
          if (triton::api.taintAssignmentRegReg(*PyRegisterOperand_AsRegisterOperand(reg1), *PyRegisterOperand_AsRegisterOperand(reg2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintMem(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintMem(): Architecture is not defined.");

        if (!PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintMem(): Expects a Memory as argument.");

        try {
          if (triton::api.taintMem(*PyMemoryOperand_AsMemoryOperand(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintReg(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintReg(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintReg(): Expects a Memory as argument.");

        try {
          if (triton::api.taintReg(*PyRegisterOperand_AsRegisterOperand(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionMemImm(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemImm(): Architecture is not defined.");

        if (!PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemImm(): Expects a Memory as argument.");

        try {
          if (triton::api.taintUnionMemImm(*PyMemoryOperand_AsMemoryOperand(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionMemMem(PyObject* self, PyObject* args) {
        PyObject* mem1 = nullptr;
        PyObject* mem2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem1, &mem2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemMem(): Architecture is not defined.");

        if (mem1 == nullptr || !PyMemoryOperand_Check(mem1))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemMem(): Expects a Memory as first argument.");

        if (mem2 == nullptr || !PyMemoryOperand_Check(mem2))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemMem(): Expects a Memory as second argument.");

        try {
          if (triton::api.taintUnionMemMem(*PyMemoryOperand_AsMemoryOperand(mem1), *PyMemoryOperand_AsMemoryOperand(mem2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionMemReg(PyObject* self, PyObject* args) {
        PyObject* mem = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &reg);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemReg(): Architecture is not defined.");

        if (mem == nullptr || !PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemReg(): Expects a Memory as first argument.");

        if (reg == nullptr || !PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemReg(): Expects a REG as second argument.");

        try {
          if (triton::api.taintUnionMemReg(*PyMemoryOperand_AsMemoryOperand(mem), *PyRegisterOperand_AsRegisterOperand(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionRegImm(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegImm(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegImm(): Expects a REG as argument.");

        try {
          if (triton::api.taintUnionRegImm(*PyRegisterOperand_AsRegisterOperand(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionRegMem(PyObject* self, PyObject* args) {
        PyObject* reg = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &mem);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegMem(): Architecture is not defined.");

        if (reg == nullptr || !PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegMem(): Expects a REG as first argument.");

        if (mem == nullptr || !PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegMem(): Expects a Memory as second argument.");

        try {
          if (triton::api.taintUnionRegMem(*PyRegisterOperand_AsRegisterOperand(reg), *PyMemoryOperand_AsMemoryOperand(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionRegReg(PyObject* self, PyObject* args) {
        PyObject* reg1 = nullptr;
        PyObject* reg2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg1, &reg2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegReg(): Architecture is not defined.");

        if (reg1 == nullptr || !PyRegisterOperand_Check(reg1))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegReg(): Expects a REG as first argument.");

        if (reg2 == nullptr || !PyRegisterOperand_Check(reg2))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegReg(): Expects a REG as second argument.");

        try {
          if (triton::api.taintUnionRegReg(*PyRegisterOperand_AsRegisterOperand(reg1), *PyRegisterOperand_AsRegisterOperand(reg2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_untaintAddr(PyObject* self, PyObject* addr) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintAddr(): Architecture is not defined.");

        if (!PyLong_Check(addr) && !PyInt_Check(addr))
          return PyErr_Format(PyExc_TypeError, "untaintAddr(): Expects an intger as argument.");

        try {
          if (triton::api.untaintAddr(PyLong_AsUint(addr)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_untaintMem(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintMem(): Architecture is not defined.");

        if (!PyMemoryOperand_Check(mem))
          return PyErr_Format(PyExc_TypeError, "untaintMem(): Expects a Memory as argument.");

        try {
          if (triton::api.untaintMem(*PyMemoryOperand_AsMemoryOperand(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_untaintReg(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintReg(): Architecture is not defined.");

        if (!PyRegisterOperand_Check(reg))
          return PyErr_Format(PyExc_TypeError, "untaintReg(): Expects a Memory as argument.");

        try {
          if (triton::api.untaintReg(*PyRegisterOperand_AsRegisterOperand(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      PyMethodDef tritonCallbacks[] = {
        {"Bitvector",                           (PyCFunction)triton_Bitvector,                              METH_VARARGS,       ""},
        {"Immediate",                           (PyCFunction)triton_Immediate,                              METH_VARARGS,       ""},
        {"Instruction",                         (PyCFunction)triton_Instruction,                            METH_NOARGS,        ""},
        {"Memory",                              (PyCFunction)triton_Memory,                                 METH_VARARGS,       ""},
        {"Register",                            (PyCFunction)triton_Register,                               METH_VARARGS,       ""},
        {"assignSymbolicExpressionToRegister",  (PyCFunction)triton_assignSymbolicExpressionToRegister,     METH_VARARGS,       ""},
        {"buildSemantics",                      (PyCFunction)triton_buildSemantics,                         METH_O,             ""},
        {"concretizeAllMem",                    (PyCFunction)triton_concretizeAllMem,                       METH_NOARGS,        ""},
        {"concretizeAllReg",                    (PyCFunction)triton_concretizeAllReg,                       METH_NOARGS,        ""},
        {"concretizeMem",                       (PyCFunction)triton_concretizeMem,                          METH_O,             ""},
        {"concretizeReg",                       (PyCFunction)triton_concretizeReg,                          METH_O,             ""},
        {"convertExprToSymVar",                 (PyCFunction)triton_convertExprToSymVar,                    METH_VARARGS,       ""},
        {"convertMemToSymVar",                  (PyCFunction)triton_convertMemToSymVar,                     METH_VARARGS,       ""},
        {"convertRegToSymVar",                  (PyCFunction)triton_convertRegToSymVar,                     METH_VARARGS,       ""},
        {"cpuInvalidReg",                       (PyCFunction)triton_cpuInvalidReg,                          METH_NOARGS,        ""},
        {"cpuNumberOfReg",                      (PyCFunction)triton_cpuNumberOfReg,                         METH_NOARGS,        ""},
        {"cpuRegBitSize",                       (PyCFunction)triton_cpuRegBitSize,                          METH_NOARGS,        ""},
        {"cpuRegSize",                          (PyCFunction)triton_cpuRegSize,                             METH_NOARGS,        ""},
        {"createSymbolicFlagExpression",        (PyCFunction)triton_createSymbolicFlagExpression,           METH_VARARGS,       ""},
        {"createSymbolicMemoryExpression",      (PyCFunction)triton_createSymbolicMemoryExpression,         METH_VARARGS,       ""},
        {"createSymbolicRegisterExpression",    (PyCFunction)triton_createSymbolicRegisterExpression,       METH_VARARGS,       ""},
        {"createSymbolicVolatileExpression",    (PyCFunction)triton_createSymbolicVolatileExpression,       METH_VARARGS,       ""},
        {"disableSymbolicOptimization",         (PyCFunction)triton_disableSymbolicOptimization,            METH_O,             ""},
        {"disassembly",                         (PyCFunction)triton_disassembly,                            METH_O,             ""},
        {"enableSymbolicEngine",                (PyCFunction)triton_enableSymbolicEngine,                   METH_O,             ""},
        {"enableSymbolicOptimization",          (PyCFunction)triton_enableSymbolicOptimization,             METH_O,             ""},
        {"enableTaintEngine",                   (PyCFunction)triton_enableTaintEngine,                      METH_O,             ""},
        {"evaluateAst",                         (PyCFunction)triton_evaluateAst,                            METH_O,             ""},
        {"getArchitecture",                     (PyCFunction)triton_getArchitecture,                        METH_NOARGS,        ""},
        {"getAstFromId",                        (PyCFunction)triton_getAstFromId,                           METH_O,             ""},
        {"getAstSummariesStats",                (PyCFunction)triton_getAstSummariesStats,                   METH_NOARGS,        ""},
        {"getFullAst",                          (PyCFunction)triton_getFullAst,                             METH_O,             ""},
        {"getFullAstFromId",                    (PyCFunction)triton_getFullAstFromId,                       METH_O,             ""},
        {"getLastMemoryValue",                  (PyCFunction)triton_getLastMemoryValue,                     METH_O,             ""},
        {"getLastRegisterValue",                (PyCFunction)triton_getLastRegisterValue,                   METH_O,             ""},
        {"getModel",                            (PyCFunction)triton_getModel,                               METH_O,             ""},
        {"getModels",                           (PyCFunction)triton_getModels,                              METH_VARARGS,       ""},
        {"getParentRegisters",                  (PyCFunction)triton_getParentRegisters,                     METH_NOARGS,        ""},
        {"getSymbolicExpressionFromId",         (PyCFunction)triton_getSymbolicExpressionFromId,            METH_O,             ""},
        {"getSymbolicExpressions",              (PyCFunction)triton_getSymbolicExpressions,                 METH_NOARGS,        ""},
        {"getSymbolicMemoryId",                 (PyCFunction)triton_getSymbolicMemoryId,                    METH_O,             ""},
        {"getSymbolicRegisterId",               (PyCFunction)triton_getSymbolicRegisterId,                  METH_O,             ""},
        {"getSymbolicVariableFromId",           (PyCFunction)triton_getSymbolicVariableFromId,              METH_O,             ""},
        {"getSymbolicVariableFromName",         (PyCFunction)triton_getSymbolicVariableFromName,            METH_O,             ""},
        {"getSymbolicVariables",                (PyCFunction)triton_getSymbolicVariables,                   METH_NOARGS,        ""},
        {"getTaintedSymbolicExpressions",       (PyCFunction)triton_getTaintedSymbolicExpressions,          METH_NOARGS,        ""},
        {"isAddrTainted",                       (PyCFunction)triton_isAddrTainted,                          METH_O,             ""},
        {"isArchitectureValid",                 (PyCFunction)triton_isArchitectureValid,                    METH_NOARGS,        ""},
        {"isMemTainted",                        (PyCFunction)triton_isMemTainted,                           METH_O,             ""},
        {"isRegTainted",                        (PyCFunction)triton_isRegTainted,                           METH_O,             ""},
        {"isSymbolicEngineEnabled",             (PyCFunction)triton_isSymbolicEngineEnabled,                METH_NOARGS,        ""},
        {"isSymbolicExpressionIdExists",        (PyCFunction)triton_isSymbolicExpressionIdExists,           METH_O,             ""},
        {"isSymbolicOptimizationEnabled",       (PyCFunction)triton_isSymbolicOptimizationEnabled,          METH_O,             ""},
        {"isTaintEngineEnabled",                (PyCFunction)triton_isTaintEngineEnabled,                   METH_NOARGS,        ""},
        {"newSymbolicExpression",               (PyCFunction)triton_newSymbolicExpression,                  METH_VARARGS,       ""},
        {"newSymbolicVariable",                 (PyCFunction)triton_newSymbolicVariable,                    METH_VARARGS,       ""},
        {"processing",                          (PyCFunction)triton_processing,                             METH_O,             ""},
        {"recordSimplificationCallback",        (PyCFunction)triton_recordSimplificationCallback,           METH_O,             ""},
        {"removeSimplificationCallback",        (PyCFunction)triton_removeSimplificationCallback,           METH_O,             ""},
        {"resetEngines",                        (PyCFunction)triton_resetEngines,                           METH_NOARGS,        ""},
        {"setArchitecture",                     (PyCFunction)triton_setArchitecture,                        METH_O,             ""},
        {"setLastMemoryValue",                  (PyCFunction)triton_setLastMemoryValue,                     METH_VARARGS,       ""},
        {"setLastRegisterValue",                (PyCFunction)triton_setLastRegisterValue,                   METH_O,             ""},
        {"setTaintMem",                         (PyCFunction)triton_setTaintMem,                            METH_VARARGS,       ""},
        {"setTaintReg",                         (PyCFunction)triton_setTaintReg,                            METH_VARARGS,       ""},
        {"simplify",                            (PyCFunction)triton_simplify,                               METH_O,             ""},
        {"taintAddr",                           (PyCFunction)triton_taintAddr,                              METH_O,             ""},
        {"taintAssignmentMemImm",               (PyCFunction)triton_taintAssignmentMemImm,                  METH_O,             ""},
        {"taintAssignmentMemMem",               (PyCFunction)triton_taintAssignmentMemMem,                  METH_VARARGS,       ""},
        {"taintAssignmentMemReg",               (PyCFunction)triton_taintAssignmentMemReg,                  METH_VARARGS,       ""},
        {"taintAssignmentRegImm",               (PyCFunction)triton_taintAssignmentRegImm,                  METH_O,             ""},
        {"taintAssignmentRegMem",               (PyCFunction)triton_taintAssignmentRegMem,                  METH_VARARGS,       ""},
        {"taintAssignmentRegReg",               (PyCFunction)triton_taintAssignmentRegReg,                  METH_VARARGS,       ""},
        {"taintMem",                            (PyCFunction)triton_taintMem,                               METH_O,             ""},
        {"taintReg",                            (PyCFunction)triton_taintReg,                               METH_O,             ""},
        {"taintUnionMemImm",                    (PyCFunction)triton_taintUnionMemImm,                       METH_O,             ""},
        {"taintUnionMemMem",                    (PyCFunction)triton_taintUnionMemMem,                       METH_VARARGS,       ""},
        {"taintUnionMemReg",                    (PyCFunction)triton_taintUnionMemReg,                       METH_VARARGS,       ""},
        {"taintUnionRegImm",                    (PyCFunction)triton_taintUnionRegImm,                       METH_O,             ""},
        {"taintUnionRegMem",                    (PyCFunction)triton_taintUnionRegMem,                       METH_VARARGS,       ""},
        {"taintUnionRegReg",                    (PyCFunction)triton_taintUnionRegReg,                       METH_VARARGS,       ""},
        {"untaintAddr",                         (PyCFunction)triton_untaintAddr,                            METH_O,             ""},
        {"untaintMem",                          (PyCFunction)triton_untaintMem,                             METH_O,             ""},
        {"untaintReg",                          (PyCFunction)triton_untaintReg,                             METH_O,             ""},
        {nullptr,                               nullptr,                                                    0,                  nullptr}

      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */

