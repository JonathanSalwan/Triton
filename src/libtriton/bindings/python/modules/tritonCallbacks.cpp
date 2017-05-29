//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/api.hpp>
#include <triton/exceptions.hpp>
#include <triton/bitsVector.hpp>
#include <triton/immediate.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/register.hpp>



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

- \ref py_AstNode_page
- \ref py_Bitvector_page
- \ref py_Elf_page
- \ref py_ElfDynamicTable_page
- \ref py_ElfHeader_page
- \ref py_ElfProgramHeader_page
- \ref py_ElfRelocationTable_page
- \ref py_ElfSectionHeader_page
- \ref py_ElfSymbolTable_page
- \ref py_Immediate_page
- \ref py_Instruction_page
- \ref py_MemoryAccess_page
- \ref py_PathConstraint_page
- \ref py_Pe_page
- \ref py_PeExportEntry_page
- \ref py_PeExportTable_page
- \ref py_PeHeader_page
- \ref py_PeImportLookup_page
- \ref py_PeImportTable_page
- \ref py_PeSectionHeader_page
- \ref py_Register_page
- \ref py_SolverModel_page
- \ref py_SymbolicExpression_page
- \ref py_SymbolicVariable_page


\subsection triton_py_api_modules Modules

- \ref ast


\subsection triton_py_api_methods Methods

- <b>void addCallback(function cb, \ref py_CALLBACK_page kind)</b><br>
Adds a callback at specific internal points. Your callback will be called each time the point is reached.

- <b>void assignSymbolicExpressionToMemory(\ref py_SymbolicExpression_page symExpr, \ref py_MemoryAccess_page mem)</b><br>
Assigns a \ref py_SymbolicExpression_page to a \ref py_MemoryAccess_page area. **Be careful**, use this function only if you know what you are doing.
The symbolic expression (`symExpr`) must be aligned to the memory access.

- <b>void assignSymbolicExpressionToRegister(\ref py_SymbolicExpression_page symExpr, \ref py_REG_page reg)</b><br>
Assigns a \ref py_SymbolicExpression_page to a \ref py_REG_page. **Be careful**, use this function only if you know what you are doing.
The symbolic expression (`symExpr`) must be aligned to the targeted size register. E.g: for SSE registers, the expression must be aligned
to 128-bits. Otherwise, you will probably get a sort mismatch error when you will solve the expression. If you want to assign an
expression to a sub-register like `AX`, `AH` or `AL`, please, craft your expression with the `concat()` and `extract()` ast functions.

- <b>bool buildSemantics(\ref py_Instruction_page inst)</b><br>
Builds the instruction semantics. Returns true if the instruction is supported. You must define an architecture before.

- <b>\ref py_AstNode_page buildSymbolicImmediate(\ref py_Immediate_page imm)</b><br>
Builds a symbolic immediate from a \ref py_Immediate_page.

- <b>\ref py_AstNode_page buildSymbolicMemory(\ref py_MemoryAccess_page mem)</b><br>
Builds a symbolic memory cell from a \ref py_MemoryAccess_page with the SSA form.

- <b>\ref py_AstNode_page buildSymbolicRegister(\ref py_REG_page reg)</b><br>
Builds a symbolic register from a \ref py_REG_page with the SSA form.

- <b>void clearPathConstraints(void)</b><br>
Clears the logical conjunction vector of path constraints.

- <b>void concretizeAllMemory(void)</b><br>
Concretizes all symbolic memory references.

- <b>void concretizeAllRegister(void)</b><br>
Concretizes all symbolic register references.

- <b>void concretizeMemory(integer addr)</b><br>
Concretizes a specific symbolic memory reference.

- <b>void concretizeMemory(\ref py_MemoryAccess_page mem)</b><br>
Concretizes a specific symbolic memory reference.

- <b>void concretizeRegister(\ref py_REG_page reg)</b><br>
Concretizes a specific symbolic register reference.

- <b>\ref py_SymbolicVariable_page convertExpressionToSymbolicVariable(integer symExprId, integer symVarSize, string comment)</b><br>
Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page convertMemoryToSymbolicVariable(\ref py_MemoryAccess_page mem, string comment)</b><br>
Converts a symbolic memory expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page convertRegisterToSymbolicVariable(\ref py_REG_page reg, string comment)</b><br>
Converts a symbolic register expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicExpression_page createSymbolicFlagExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_REG_page flag, string comment)</b><br>
Returns the new symbolic register expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicMemoryExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_MemoryAccess_page mem, string comment)</b><br>
Returns the new symbolic memory expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicRegisterExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_REG_page reg, string comment)</b><br>
Returns the new symbolic register expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicVolatileExpression (\ref py_Instruction_page inst, \ref py_AstNode_page node, string comment)</b><br>
Returns the new symbolic volatile expression and links this expression to the instruction.

- <b>void disassembly(\ref py_Instruction_page inst)</b><br>
Disassembles the instruction and setup operands. You must define an architecture before.

- <b>void enableMode(\ref py_MODE_page mode, bool flag)</b><br>
Enables or disables a specific mode.

- <b>void enableSymbolicEngine(bool flag)</b><br>
Enables or disables the symbolic execution engine.

- <b>void enableTaintEngine(bool flag)</b><br>
Enables or disables the taint engine.

- <b>integer evaluateAstViaZ3(\ref py_AstNode_page node)</b><br>
Evaluates an AST via Z3 and returns the symbolic value.

- <b>[\ref py_Register_page, ...] getAllRegisters(void)</b><br>
Returns the list of all registers. Each item of this list is a \ref py_Register_page.

- <b>\ref py_ARCH_page getArchitecture(void)</b><br>
Returns the current architecture used.

- <b>dict getAstDictionariesStats(void)</b><br>
Returns a dictionary which contains all information about number of nodes allocated via AST dictionaries.

- <b>\ref py_AstNode_page getAstFromId(integer symExprId)</b><br>
Returns the partial AST from a symbolic expression id.

- <b>\ref py_AST_REPRESENTATION_page getAstRepresentationMode(void)</b><br>
Returns the current AST representation mode.

- <b>bytes getConcreteMemoryAreaValue(integer baseAddr, integer size)</b><br>
Returns the concrete value of a memory area.

- <b>integer getConcreteMemoryValue(intger addr)</b><br>
Returns the concrete value of a memory cell.

- <b>integer getConcreteMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the concrete value of memory cells.

- <b>integer getConcreteRegisterValue(\ref py_REG_page reg)</b><br>
Returns the concrete value of a register.

- <b>\ref py_AstNode_page getFullAst(\ref py_AstNode_page node)</b><br>
Returns the full AST without SSA form from a given root node.

- <b>\ref py_AstNode_page getFullAstFromId(integer symExprId)</b><br>
Returns the full AST without SSA form from a symbolic expression id.

- <b>dict getModel(\ref py_AstNode_page node)</b><br>
Computes and returns a model as a dictionary of {integer symVarId : \ref py_SolverModel_page model} from a symbolic constraint.

- <b>[dict, ...] getModels(\ref py_AstNode_page node, integer limit)</b><br>
Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.

- <b>[\ref py_Register_page, ...] getParentRegisters(void)</b><br>
Returns the list of parent registers. Each item of this list is a \ref py_Register_page.

- <b>[\ref py_PathConstraint_page, ...] getPathConstraints(void)</b><br>
Returns the logical conjunction vector of path constraints as list of \ref py_PathConstraint_page.

- <b>\ref py_AstNode_page getPathConstraintsAst(void)</b><br>
Returns the logical conjunction AST of path constraints.

- <b>integer getRegisterBitSize(void)</b><br>
Returns the max size (in bit) of the CPU register (GPR).

- <b>integer getRegisterSize(void)</b><br>
Returns the max size (in byte) of the CPU register (GPR).

- <b>\ref py_SymbolicExpression_page getSymbolicExpressionFromId(intger symExprId)</b><br>
Returns the symbolic expression corresponding to an id.

- <b>dict getSymbolicExpressions(void)</b><br>
Returns all symbolic expressions as a dictionary of {integer SymExprId : \ref py_SymbolicExpression_page expr}.

- <b>dict getSymbolicMemory(void)</b><br>
Returns the map of symbolic memory as {integer address : \ref py_SymbolicExpression_page expr}.

- <b>integer getSymbolicMemoryId(intger addr)</b><br>
Returns the symbolic expression id corresponding to a memory address.

- <b>integer getSymbolicMemoryValue(intger addr)</b><br>
Returns the symbolic memory value.

- <b>integer getSymbolicMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the symbolic memory value.

- <b>dict getSymbolicRegisters(void)</b><br>
Returns the map of symbolic register as {\ref py_REG_page reg : \ref py_SymbolicExpression_page expr}.

- <b>integer getSymbolicRegisterId(\ref py_REG_page reg)</b><br>
Returns the symbolic expression id corresponding to a register.

- <b>integer getSymbolicRegisterValue(\ref py_REG_page reg)</b><br>
Returns the symbolic register value.

- <b>\ref py_SymbolicVariable_page getSymbolicVariableFromId(integer symVarId)</b><br>
Returns the symbolic variable corresponding to a symbolic variable id.

- <b>\ref py_SymbolicVariable_page getSymbolicVariableFromName(string symVarName)</b><br>
Returns the symbolic variable corresponding to a symbolic variable name.

- <b>dict getSymbolicVariables(void)</b><br>
Returns all symbolic variable as a dictionary of {integer SymVarId : \ref py_SymbolicVariable_page var}.

- <b>[intger, ...] getTaintedMemory(void)</b><br>
Returns the list of all tainted addresses.

- <b>[\ref py_Register_page, ...] getTaintedRegisters(void)</b><br>
Returns the list of all tainted registers.

- <b>[\ref py_SymbolicExpression_page, ...] getTaintedSymbolicExpressions(void)</b><br>
Returns the list of all tainted symbolic expressions.

- <b>bool isArchitectureValid(void)</b><br>
Returns true if the architecture is valid.

- <b>bool isFlag(\ref py_REG_page reg)</b><br>
Returns true if the register id is a flag.

- <b>bool isMemoryMapped(integer baseAddr, integer size=1)</b><br>
Returns true if the range `[baseAddr:size]` is mapped into the internal memory representation.

- <b>bool isMemorySymbolized(integer addr)</b><br>
Returns true if the memory cell expression contains a symbolic variable.

- <b>bool isMemorySymbolized(\ref py_MemoryAccess_page mem)</b><br>
Returns true if memory cell expressions contain symbolic variables.

- <b>bool isMemoryTainted(integer addr)</b><br>
Returns true if the address is tainted.

- <b>bool isMemoryTainted(\ref py_MemoryAccess_page mem)</b><br>
Returns true if the memory is tainted.

- <b>bool isModeEnabled(\ref py_MODE_page mode)</b><br>
Returns true if the mode is enabled.

- <b>bool isRegister(\ref py_REG_page reg)</b><br>
Returns true if the register id is a register (see also isFlag()).

- <b>bool isRegisterSymbolized(\ref py_REG_page reg)</b><br>
Returns true if the register expression contains a symbolic variable.

- <b>bool isRegisterTainted(\ref py_REG_page reg)</b><br>
Returns true if the register is tainted.

- <b>bool isRegisterValid(\ref py_REG_page reg)</b><br>
Returns true if the register id is valid.

- <b>bool isSymbolicEngineEnabled(void)</b><br>
Returns true if the symbolic execution engine is enabled.

- <b>bool isSymbolicExpressionIdExists(integer symExprId)</b><br>
Returns true if the symbolic expression id exists.

- <b>bool isTaintEngineEnabled(void)</b><br>
Returns true if the taint engine is enabled.

- <b>\ref py_SymbolicExpression_page newSymbolicExpression(\ref py_AstNode_page node, string comment)</b><br>
Returns a new symbolic expression. Note that if there are simplification passes recorded, simplifications will be applied.

- <b>\ref py_SymbolicVariable_page newSymbolicVariable(intger varSize, string comment)</b><br>
Returns a new symbolic variable.

- <b>bool processing(\ref py_Instruction_page inst)</b><br>
Processes an instruction and updates engines according to the instruction semantics. Returns true if the instruction is supported. You must define an architecture before.

- <b>void removeAllCallbacks(void)</b><br>
Removes all recorded callbacks.

- <b>void removeCallback(function cb, \ref py_CALLBACK_page kind)</b><br>
Removes a recorded callback.

- <b>void resetEngines(void)</b><br>
Resets everything.

- <b>void setArchitecture(\ref py_ARCH_page arch)</b><br>
Initializes an architecture. This function must be called before any call to the rest of the API.

- <b>void setAstRepresentationMode(\ref py_AST_REPRESENTATION_page mode)</b><br>
Sets the AST representation mode.

- <b>void setConcreteMemoryAreaValue(integer baseAddr, [integer,])</b><br>
Sets the concrete value of a memory area. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteMemoryAreaValue(integer baseAddr, bytes opcodes)</b><br>
Sets the concrete value of a memory area. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteMemoryValue(integer addr, integer value)</b><br>
Sets the concrete value of a memory cell. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Sets the concrete value of memory cells. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteRegisterValue(\ref py_REG_page reg)</b><br>
Sets the concrete value of a register. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>bool setTaintMemory(\ref py_MemoryAccess_page mem, bool flag)</b><br>
Sets the targeted memory as tainted or not. Returns true if the memory is still tainted.

- <b>bool setTaintRegister(\ref py_REG_page reg, bool flag)</b><br>
Sets the targeted register as tainted or not. Returns true if the register is still tainted.

- <b>\ref py_AstNode_page simplify(\ref py_AstNode_page node, bool z3=False)</b><br>
Calls all simplification callbacks recorded and returns a new simplified node. If the `z3` flag is
set to True, Triton will use z3 to simplify the given `node` before to call its recorded callbacks.

- <b>dict sliceExpressions(\ref py_SymbolicExpression_page expr)</b><br>
Slices expressions from a given one (backward slicing) and returns all symbolic expressions as a dictionary of {integer SymExprId : \ref py_SymbolicExpression_page expr}.

- <b>bool taintAssignmentMemoryImmediate(\ref py_MemoryAccess_page memDst)</b><br>
Taints `memDst` with an assignment - `memDst` is untained. Returns true if the `memDst` is still tainted.

- <b>bool taintAssignmentMemoryMemory(\ref py_MemoryAccess_page memDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an assignment - `memDst` is tainted if `memSrc` is tainted, otherwise
`memDst` is untained. Returns true if `memDst` is tainted.

- <b>bool taintAssignmentMemoryRegister(\ref py_MemoryAccess_page memDst, \ref py_REG_page regSrc)</b><br>
Taints `memDst` from `regSrc` with an assignment - `memDst` is tainted if `regSrc` is tainted, otherwise
`memDst` is untained. Return true if `memDst` is tainted.

- <b>bool taintAssignmentRegisterImmediate(\ref py_REG_page regDst)</b><br>
Taints `regDst` with an assignment - `regDst` is untained. Returns true if `reDst` is still tainted.

- <b>bool taintAssignmentRegisterMemory(\ref py_REG_page regDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `regDst` from `MemSrc` with an assignment - `regDst` is tainted if `memSrc` is tainted, otherwise
`regDst` is untained. Return true if `regDst` is tainted.

- <b>bool taintAssignmentRegisterRegister(\ref py_REG_page regDst, \ref py_REG_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an assignment - `regDst` is tainted if `regSrc` is tainted, otherwise
`regDst` is untained. Return true if `regDst` is tainted.

- <b>bool taintMemory(intger addr)</b><br>
Taints an address. Returns true if the address is tainted.

- <b>bool taintMemory(\ref py_MemoryAccess_page mem)</b><br>
Taints a memory. Returns true if the memory is tainted.

- <b>bool taintRegister(\ref py_REG_page reg)</b><br>
Taints a register. Returns true if the register is tainted.

- <b>bool taintUnionMemoryImmediate(\ref py_MemoryAccess_page memDst)</b><br>
Taints `memDst` with an union - `memDst` does not changes. Returns true if `memDst` is tainted.

- <b>bool taintUnionMemoryMemory(\ref py_MemoryAccess_page memDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an union - `memDst` is tainted if `memDst` or `memSrc` are
tainted. Returns true if `memDst` is tainted.

- <b>bool taintUnionMemoryRegister(\ref py_MemoryAccess_page memDst, \ref py_REG_page regSrc)</b><br>
Taints `memDst` from `RegSrc` with an union - `memDst` is tainted if `memDst` or `regSrc` are
tainted. Returns true if `memDst` is tainted.

- <b>bool taintUnionRegisterImmediate(\ref py_REG_page regDst)</b><br>
Taints `regDst` with an union - `regDst` does not changes. Returns true if `regDst` is tainted.

- <b>bool taintUnionRegisterMemory(\ref py_REG_page regDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `regDst` from `memSrc` with an union - `regDst` is tainted if `regDst` or `memSrc` are
tainted. Returns true if `regDst` is tainted.

- <b>bool taintUnionRegisterRegister(\ref py_REG_page regDst, \ref py_REG_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an union - `regDst` is tainted if `regDst` or `regSrc` are
tainted. Returns true if `regDst` is tainted.

- <b>void unmapMemory(integer baseAddr, integer size=1)</b><br>
Removes the range `[baseAddr:size]` from the internal memory representation.

- <b>bool untaintMemory(intger addr)</b><br>
Untaints an address. Returns true if the address is still tainted.

- <b>bool untaintMemory(\ref py_MemoryAccess_page mem)</b><br>
Untaints a memory. Returns true if the memory is still tainted.

- <b>bool untaintRegister(\ref py_REG_page reg)</b><br>
Untaints a register. Returns true if the register is still tainted.


\subsection triton_py_api_namespaces Namespaces

- \ref py_ARCH_page
- \ref py_AST_NODE_page
- \ref py_AST_REPRESENTATION_page
- \ref py_CALLBACK_page
- \ref py_CPUSIZE_page
- \ref py_ELF_page
- \ref py_MODE_page
- \ref py_OPCODE_page
- \ref py_OPERAND_page
- \ref py_PE_page
- \ref py_REG_page
- \ref py_SYMEXPR_page
- \ref py_SYSCALL_page
- \ref py_VERSION_page

\section pintool_py_api Python API - Methods and namespaces of the pintool
<hr>

This project is shipped with a Pin \ref Tracer_page which can be compile with the `cmake` flag `-DPINTOOL=on`.
Then, the pintool must be used like this:


~~~~~~~~~~~~~{.sh}
$ ./triton <your_script.py> <your_targeted_binary>
~~~~~~~~~~~~~

Your script must contains the pintool and triton imports.

~~~~~~~~~~~~~{.py}
>>> from triton import *
>>> from pintool import *
~~~~~~~~~~~~~


\subsection pintool_py_api_methods Methods

- <b>bool checkReadAccess(integer addr)</b><br>
Checks whether the memory page which contains this address has a read access protection.

- <b>bool checkWriteAccess(integer addr)</b><br>
Checks whether the memory page which contains this address has a write access protection.

- <b>void detachProcess(void)</b><br>
Detachs the pintool from the targeted process. The control flow is returned to the original uninstrumented code and
the application is natively executed.

- <b>void disableSnapshot(void)</b><br>
Disables the snapshot engine. When you have done with the `tracer::pintool::Snapshot::restoreSnapshot()` function,
you may use this function to improve performance. Then, the snapshot engine will be enable at the next
`tracer::pintool::Snapshot::takeSnapshot()` call.

- <b>integer getCurrentMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the memory value from a \ref py_MemoryAccess_page.

- <b>integer getCurrentMemoryValue(integer addr)</b><br>
Returns the memory value from the address.

- <b>integer getCurrentMemoryValue(integer addr, integer readSize)</b><br>
Returns the memory value according to the `readSize` from the address.

- <b>integer getCurrentRegisterValue(\ref py_REG_page reg)</b><br>
Returns the register value from a \ref py_REG_page.

- <b>string getImageName(integer addr)</b><br>
Returns the image name from a given address. Returns an empty string if not found.

- <b>string getRoutineName(integer addr)</b><br>
Returns the routine name from a given address. Returns an empty string if not found.

- <b>integer getSyscallArgument(\ref py_STANDARD_page std, integer argNum)</b><br>
Returns the argument value of the system call which is executed in the current context. It is a user's responsibility to make sure that the
current instruction is a syscall. This function must be used in a `SYSCALL_ENTRY` \ref py_INSERT_POINT_page.

- <b>integer getSyscallNumber(\ref py_STANDARD_page std)</b><br>
Returns the syscall number of the system call which is executed in the current context. It is a user's responsibility to make sure that the
current instruction is a syscall. This function must be used in a `SYSCALL_ENTRY` \ref py_INSERT_POINT_page.

- <b>intger getSyscallReturn(\ref py_STANDARD_page std)</b><br>
Returns the result of the syscall. It is a user's responsibility to make sure that the current context represents
the state of a system call after its execution. This function must be used in a `SYSCALL_EXIT` \ref py_INSERT_POINT_page.

- <b>void insertCall(function, \ref py_INSERT_POINT_page type)</b><br>
Inserts a call before and after several cases. All code executed into a callback function are executed during the
instrumentation.

- <b>bool isSnapshotEnabled(void)</b><br>
Returns true if the snapshot engine is enabled.

- <b>void restoreSnapshot(void)</b><br>
Restores the last snpahost taken. Check the `tracer::pintool::Snapshot::takeSnapshot()` function. Note that this function
have to execute a new context registers, so `RIP` will be modified and your callback stopped
(checkout the [Pin API](https://software.intel.com/sites/landingpage/pintool/docs/71313/Pin/html/group__CONTEXT__API.html#g4e6408c641479c22918a888d95ca1930)).

- <b>void runProgram(void)</b><br>
Starts the binary instrumentation over Pin.

- <b>void setCurrentMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Sets the current memory value from a \ref py_MemoryAccess_page.

- <b>void setCurrentMemoryValue(\ref py_MemoryAccess_page mem, integer value)</b><br>
Sets the current memory value from a \ref py_MemoryAccess_page.

- <b>void setCurrentMemoryValue(integer addr, integer value)</b><br>
Sets the current memory value from an address.

- <b>void setCurrentRegisterValue(\ref py_Register_page reg)</b><br>
Sets the current register value from a \ref py_Register_page. This method can only be called into a `BEFORE_SYMPROC`
and `AFTER` callback. This method also synchronizes the Triton's register.

- <b>void setCurrentRegisterValue(\ref py_Register_page reg, integer value)</b><br>
Sets the current register value from a \ref py_Register_page. This method can only be called into a `BEFORE_SYMPROC`
and `AFTER` callback. This method also synchronizes the Triton's register.

- <b>void setupImageBlacklist([string, ...])</b><br>
Setups a blacklist of image names, it means that these images will not be instrumented and executed natively.

- <b>void setupImageWhitelist([string, ...])</b><br>
Setups a whitelist of image names, it means that these images will be instrumented and all other images will be
executed natively.

- <b>void startAnalysisFromAddress(integer addr)</b><br>
Starts the instrumentation at a specific address.

- <b>void startAnalysisFromEntry(void)</b><br>
Starts the instrumentation at the entry point.

- <b>void startAnalysisFromOffset(integer offset)</b><br>
Starts the instrumentation at a specific offset in the binary

- <b>void startAnalysisFromSymbol(string symbol)</b><br>
Starts the instrumentation at a specific symbol.

- <b>void stopAnalysisFromAddress(integer addr)</b><br>
Stops the instrumentation at a specific address.

- <b>void stopAnalysisFromOffset(integer offset)</b><br>
Stops the instrumentation at a specific offset.

- <b>void takeSnapshot(void)</b><br>
Creates a snaphost at this program point.

\subsection pintool_py_api_namespaces Namespaces

- \ref py_INSERT_POINT_page
- \ref py_STANDARD_page

*/



namespace triton {
  namespace bindings {
    namespace python {

      static PyObject* triton_Elf(PyObject* self, PyObject* path) {
        /* Check if the first arg is a integer */
        if (path == nullptr || !PyString_Check(path))
          return PyErr_Format(PyExc_TypeError, "Elf(): Expects a string as first argument.");

        try {
          return PyElf(PyString_AsString(path));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_Pe(PyObject* self, PyObject* path) {
        /* Check if the first arg is a integer */
        if (path == nullptr || !PyString_Check(path))
          return PyErr_Format(PyExc_TypeError, "Pe(): Expects a string as first argument.");

        try {
          return PyPe(PyString_AsString(path));
        }
        catch (const triton::exceptions::Exception& e) {
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
          triton::arch::Immediate imm(PyLong_AsUint64(value), PyLong_AsUint32(size));
          return PyImmediate(imm);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_Instruction(PyObject* self, PyObject* args) {
        PyObject* opcodes = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|O", &opcodes);

        if (opcodes == nullptr)
          return PyInstruction();

        if (!PyBytes_Check(opcodes))
          return PyErr_Format(PyExc_TypeError, "Instruction(): Expected bytes as argument.");

        try {
          triton::uint8* opc  = reinterpret_cast<triton::uint8*>(PyBytes_AsString(opcodes));
          triton::uint32 size = static_cast<triton::uint32>(PyBytes_Size(opcodes));
          return PyInstruction(opc, size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_MemoryAccess(PyObject* self, PyObject* args) {
        PyObject* address       = nullptr;
        PyObject* size          = nullptr;
        PyObject* concreteValue = nullptr;
        triton::uint512 cv      = 0;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &address, &size, &concreteValue);

        /* Check if the first arg is a integer */
        if (address == nullptr || (!PyLong_Check(address) && !PyInt_Check(address)))
          return PyErr_Format(PyExc_TypeError, "MemoryAccess(): Expects an integer as first argument.");

        /* Check if the second arg is a integer */
        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "MemoryAccess(): Expects an integer as second argument.");

        /* Check if the third arg is a integer */
        if (concreteValue != nullptr && (!PyLong_Check(concreteValue) && !PyInt_Check(concreteValue)))
          return PyErr_Format(PyExc_TypeError, "MemoryAccess(): Expects an integer as third argument.");

        if (concreteValue != nullptr)
          cv = PyLong_AsUint512(concreteValue);

        try {
          if (concreteValue == nullptr){
            triton::arch::MemoryAccess mem(PyLong_AsUint64(address), PyLong_AsUint32(size));
            return PyMemoryAccess(mem);
          }

          triton::arch::MemoryAccess mem(PyLong_AsUint64(address), PyLong_AsUint32(size), cv);
          return PyMemoryAccess(mem);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_Register(PyObject* self, PyObject* args) {
        PyObject* concreteValue = nullptr;
        PyObject* regIn         = nullptr;
        triton::uint512 cv      = 0;
        triton::uint32 rid      = 0;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &regIn, &concreteValue);

        /* Check if the second arg is a integer */
        if (concreteValue != nullptr && (!PyLong_Check(concreteValue) && !PyInt_Check(concreteValue)))
          return PyErr_Format(PyExc_TypeError, "Register(): Expects an integer as second argument.");

        if (concreteValue != nullptr)
          cv = PyLong_AsUint512(concreteValue);

        /* Check if the first arg is a Register */
        if (regIn != nullptr && PyRegister_Check(regIn))
          rid = PyRegister_AsRegister(regIn)->getId();

        /* Check if the first arg is a Register */
        else if (regIn != nullptr && (PyLong_Check(regIn) || PyInt_Check(regIn)))
          rid = PyLong_AsUint32(regIn);

        /* Invalid firt arg */
        else
          return PyErr_Format(PyExc_TypeError, "Register(): Expects a Register or an id register as first argument.");

        try {
          if (concreteValue == nullptr) {
            triton::arch::Register regOut(rid);
            return PyRegister(regOut);
          }

          triton::arch::Register regOut(rid, cv);
          return PyRegister(regOut);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_addCallback(PyObject* self, PyObject* args) {
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &function, &mode);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "addCallback(): Architecture is not defined.");

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "addCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "addCallback(): Expects a CALLBACK as second argument.");

        try {
          switch (static_cast<triton::callbacks::callback_e>(PyLong_AsUint32(mode))) {

            case callbacks::GET_CONCRETE_MEMORY_VALUE:
              triton::api.addCallback(callbacks::getConcreteMemoryValueCallback([function](triton::arch::MemoryAccess& mem) {
                /********* Lambda *********/
                /* Create function args */
                PyObject* args = triton::bindings::python::xPyTuple_New(1);
                PyTuple_SetItem(args, 0, triton::bindings::python::PyMemoryAccess(mem));

                /* Call the callback */
                PyObject* ret = PyObject_CallObject(function, args);

                /* Check the call */
                if (ret == nullptr) {
                  PyErr_Print();
                  throw triton::exceptions::Callbacks("Callbacks::processCallbacks(GET_CONCRETE_MEMORY_VALUE): Fail to call the python callback.");
                }

                Py_DECREF(args);
                /********* End of lambda *********/
              }, function));
              break;

            case callbacks::GET_CONCRETE_REGISTER_VALUE:
              triton::api.addCallback(callbacks::getConcreteRegisterValueCallback([function](triton::arch::Register& reg) {
                /********* Lambda *********/
                /* Create function args */
                PyObject* args = triton::bindings::python::xPyTuple_New(1);
                PyTuple_SetItem(args, 0, triton::bindings::python::PyRegister(reg));

                /* Call the callback */
                PyObject* ret = PyObject_CallObject(function, args);

                /* Check the call */
                if (ret == nullptr) {
                  PyErr_Print();
                  throw triton::exceptions::Callbacks("Callbacks::processCallbacks(GET_CONCRETE_MEMORY_VALUE): Fail to call the python callback.");
                }

                Py_DECREF(args);
                /********* End of lambda *********/
              }, function));
              break;

            case callbacks::SYMBOLIC_SIMPLIFICATION:
              triton::api.addCallback(callbacks::symbolicSimplificationCallback([function](triton::ast::AbstractNode* node) {
                /********* Lambda *********/
                PyObject* args = triton::bindings::python::xPyTuple_New(1);
                PyTuple_SetItem(args, 0, triton::bindings::python::PyAstNode(node));

                /* Call the callback */
                PyObject* ret = PyObject_CallObject(function, args);

                /* Check the call */
                if (ret == nullptr) {
                  PyErr_Print();
                  throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): Fail to call the python callback.");
                }

                /* Check if the callback has returned a AbstractNode */
                if (!PyAstNode_Check(ret))
                  throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): You must return a AstNode object.");

                /* Update node */
                node = PyAstNode_AsAstNode(ret);
                Py_DECREF(args);
                return node;
                /********* End of lambda *********/
              }, function));
              break;

            default:
              return PyErr_Format(PyExc_TypeError, "Callbacks::addCallback(): Invalid kind of callback.");
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_assignSymbolicExpressionToMemory(PyObject* self, PyObject* args) {
        PyObject* se  = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &se, &mem);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Architecture is not defined.");

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Expects a SymbolicExpression as first argument.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Expects a MemoryAccess as second argument.");

        triton::engines::symbolic::SymbolicExpression* arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::MemoryAccess arg2 = *PyMemoryAccess_AsMemoryAccess(mem);

        try {
          triton::api.assignSymbolicExpressionToMemory(arg1, arg2);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
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

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a REG as second argument.");

        triton::engines::symbolic::SymbolicExpression* arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::Register arg2 = *PyRegister_AsRegister(reg);

        try {
          triton::api.assignSymbolicExpressionToRegister(arg1, arg2);
        }
        catch (const triton::exceptions::Exception& e) {
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
          if (triton::api.buildSemantics(*PyInstruction_AsInstruction(inst)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_buildSymbolicImmediate(PyObject* self, PyObject* imm) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSymbolicImmediate(): Architecture is not defined.");

        if (!PyImmediate_Check(imm))
          return PyErr_Format(PyExc_TypeError, "buildSymbolicImmediate(): Expects an Immediate as argument.");

        try {
          return PyAstNode(triton::api.buildSymbolicImmediate(*PyImmediate_AsImmediate(imm)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_buildSymbolicMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSymbolicMemory(): Architecture is not defined.");

        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "buildSymbolicMemory(): Expects an MemoryAccess as argument.");

        try {
          return PyAstNode(triton::api.buildSymbolicMemory(*PyMemoryAccess_AsMemoryAccess(mem)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_buildSymbolicRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSymbolicRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "buildSymbolicRegister(): Expects an Register as argument.");

        try {
          return PyAstNode(triton::api.buildSymbolicRegister(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_clearPathConstraints(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "clearPathConstraints(): Architecture is not defined.");
        triton::api.clearPathConstraints();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeAllMemory(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeAllMemory(): Architecture is not defined.");
        triton::api.concretizeAllMemory();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeAllRegister(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeAllRegister(): Architecture is not defined.");
        triton::api.concretizeAllRegister();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeMemory(): Architecture is not defined.");

        /* If mem is an address */
        if (PyLong_Check(mem) || PyInt_Check(mem)) {
          try {
            triton::api.concretizeMemory(PyLong_AsUint64(mem));
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* If mem is a MemoryAccess */
        else if (PyMemoryAccess_Check(mem)) {
          try {
            triton::api.concretizeMemory(*PyMemoryAccess_AsMemoryAccess(mem));
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* Invalid parameter */
        else
          return PyErr_Format(PyExc_TypeError, "concretizeMemory(): Expects an integer or MemoryAccess as argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_concretizeRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "concretizeRegister(): Expects a REG as argument.");

        try {
          triton::api.concretizeRegister(*PyRegister_AsRegister(reg));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_convertExpressionToSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* exprId        = nullptr;
        PyObject* symVarSize    = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &exprId, &symVarSize, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Architecture is not defined.");

        if (exprId == nullptr || (!PyLong_Check(exprId) && !PyInt_Check(exprId)))
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Expects an integer as first argument.");

        if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Expects an integer as second argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.convertExpressionToSymbolicVariable(PyLong_AsUsize(exprId), PyLong_AsUint32(symVarSize), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_convertMemoryToSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* mem           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertMemoryToSymbolicVariable(): Architecture is not defined.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "convertMemoryToSymbolicVariable(): Expects a MemoryAccess as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertMemoryToSymbolicVariable(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.convertMemoryToSymbolicVariable(*PyMemoryAccess_AsMemoryAccess(mem), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_convertRegisterToSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* reg           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &comment);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertRegisterToSymbolicVariable(): Architecture is not defined.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "convertRegisterToSymbolicVariable(): Expects a REG as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertRegisterToSymbolicVariable(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(triton::api.convertRegisterToSymbolicVariable(*PyRegister_AsRegister(reg), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
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

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a AstNode as second argument.");

        if (flag == nullptr || (!PyRegister_Check(flag)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a REG as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::AbstractNode *arg2 = PyAstNode_AsAstNode(node);
        triton::arch::Register arg3 = *PyRegister_AsRegister(flag);

        try {
          return PySymbolicExpression(triton::api.createSymbolicFlagExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
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

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects a AstNode as second argument.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects a MemoryAccess as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::AbstractNode *arg2 = PyAstNode_AsAstNode(node);
        triton::arch::MemoryAccess arg3 = *PyMemoryAccess_AsMemoryAccess(mem);

        try {
          return PySymbolicExpression(triton::api.createSymbolicMemoryExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
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

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a AstNode as second argument.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a REG as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::AbstractNode *arg2 = PyAstNode_AsAstNode(node);
        triton::arch::Register arg3 = *PyRegister_AsRegister(reg);

        try {
          return PySymbolicExpression(triton::api.createSymbolicRegisterExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
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

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects a AstNode as second argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::AbstractNode *arg2 = PyAstNode_AsAstNode(node);

        try {
          return PySymbolicExpression(triton::api.createSymbolicVolatileExpression(arg1, arg2, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_enableMode(PyObject* self, PyObject* args) {
        PyObject* mode = nullptr;
        PyObject* flag = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mode, &flag);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableMode(): Architecture is not defined.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "enableMode(): Expects a MODE as argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "enableMode(): Expects an boolean flag as second argument.");

        try {
          triton::api.enableMode(static_cast<enum triton::modes::mode_e>(PyLong_AsUint32(mode)), PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::Exception& e) {
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
          triton::api.enableSymbolicEngine(PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::Exception& e) {
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
          triton::api.enableTaintEngine(PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_evaluateAstViaZ3(PyObject* self, PyObject* node) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "evaluateAstViaZ3(): Architecture is not defined.");

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "evaluateAstViaZ3(): Expects a AstNode as argument.");

        try {
          return PyLong_FromUint512(triton::api.evaluateAstViaZ3(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        catch (const z3::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.msg());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_getAllRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAllRegisters(): Architecture is not defined.");

        try {
          triton::uint32 index = 0;
          std::set<triton::arch::Register*> reg = triton::api.getAllRegisters();

          ret = xPyList_New(reg.size());
          for (auto it = reg.begin(); it != reg.end(); it++)
            PyList_SetItem(ret, index++, PyRegister(**it));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getArchitecture(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint32(triton::api.getArchitecture());
      }


      static PyObject* triton_getAstDictionariesStats(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstDictionariesStats(): Architecture is not defined.");

        try {
          std::map<std::string, triton::usize> stats = triton::api.getAstDictionariesStats();

          ret = xPyDict_New();
          for (auto it = stats.begin(); it != stats.end(); it++)
            PyDict_SetItem(ret, PyString_FromString(it->first.c_str()), PyLong_FromUsize(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getAstFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getAstFromId(): Expects an integer as argument.");

        try {
          return PyAstNode(triton::api.getAstFromId(PyLong_AsUsize(symExprId)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getAstRepresentationMode(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstRepresentationMode(): Architecture is not defined.");
        return PyLong_FromUint32(triton::api.getAstRepresentationMode());
      }


      static PyObject* triton_getConcreteMemoryAreaValue(PyObject* self, PyObject* args) {
        triton::uint8*  area = nullptr;
        PyObject*       ret  = nullptr;
        PyObject*       addr = nullptr;
        PyObject*       size = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &addr, &size);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteMemoryAreaValue(): Architecture is not defined.");

        try {
          std::vector<triton::uint8> vv = triton::api.getConcreteMemoryAreaValue(PyLong_AsUint64(addr), PyLong_AsUsize(size));
          area = new triton::uint8[vv.size()];

          for (triton::usize index = 0; index < vv.size(); index++)
            area[index] = vv[index];

          ret = PyBytes_FromStringAndSize(reinterpret_cast<const char*>(area), vv.size());
          delete[] area;
          return ret;

        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getConcreteMemoryValue(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteMemoryValue(): Architecture is not defined.");

        try {
          if (PyLong_Check(mem) || PyInt_Check(mem))
              return PyLong_FromUint512(triton::api.getConcreteMemoryValue(PyLong_AsUint64(mem)));
          else if (PyMemoryAccess_Check(mem))
              return PyLong_FromUint512(triton::api.getConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
          else
            return PyErr_Format(PyExc_TypeError, "getConcreteMemoryValue(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getConcreteRegisterValue(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteRegisterValue(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getConcreteRegisterValue(): Expects a REG as argument.");

        try {
          return PyLong_FromUint512(triton::api.getConcreteRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getFullAst(PyObject* self, PyObject* node) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getFullAst(): Architecture is not defined.");

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getFullAst(): Expects a AstNode as argument.");

        try {
          return PyAstNode(triton::api.getFullAst(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::Exception& e) {
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
          return PyAstNode(triton::api.getFullAstFromId(PyLong_AsUsize(symExprId)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getModel(PyObject* self, PyObject* node) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getModel(): Architecture is not defined.");

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModel(): Expects a AstNode as argument.");

        try {
          ret = xPyDict_New();
          auto model = triton::api.getModel(PyAstNode_AsAstNode(node));
          for (auto it = model.begin(); it != model.end(); it++) {
            PyDict_SetItem(ret, PyLong_FromUint32(it->first), PySolverModel(it->second));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getModels(PyObject* self, PyObject* args) {
        PyObject* ret   = nullptr;
        PyObject* node  = nullptr;
        PyObject* limit = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &limit);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getModels(): Architecture is not defined.");

        if (node == nullptr || !PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModels(): Expects a AstNode as first argument.");

        if (limit == nullptr || (!PyLong_Check(limit) && !PyInt_Check(limit)))
          return PyErr_Format(PyExc_TypeError, "getModels(): Expects an integer as second argument.");

        try {
          auto models = triton::api.getModels(PyAstNode_AsAstNode(node), PyLong_AsUint32(limit));
          triton::uint32 index = 0;

          ret = xPyList_New(models.size());
          for (auto it = models.begin(); it != models.end(); it++) {
            PyObject* mdict = xPyDict_New();
            auto model = *it;

            for (auto it2 = model.begin(); it2 != model.end(); it2++) {
              PyDict_SetItem(mdict, PyLong_FromUint32(it2->first), PySolverModel(it2->second));
            }
            if (model.size() > 0)
              PyList_SetItem(ret, index++, mdict);
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getParentRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getParentRegisters(): Architecture is not defined.");

        try {
          triton::uint32 index = 0;
          std::set<triton::arch::Register*> reg = triton::api.getParentRegisters();
          ret = xPyList_New(reg.size());

          for (auto it = reg.begin(); it != reg.end(); it++)
            PyList_SetItem(ret, index++, PyRegister(**it));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getPathConstraints(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getPathConstraintsAst(): Architecture is not defined.");

        try {
          triton::uint32 index = 0;
          const std::vector<triton::engines::symbolic::PathConstraint>& pc = triton::api.getPathConstraints();
          ret = xPyList_New(pc.size());

          for (auto it = pc.begin(); it != pc.end(); it++)
            PyList_SetItem(ret, index++, PyPathConstraint(*it));

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getPathConstraintsAst(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getPathConstraintsAst(): Architecture is not defined.");

        try {
          return PyAstNode(triton::api.getPathConstraintsAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getRegisterBitSize(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint32(triton::api.getRegisterBitSize());
      }


      static PyObject* triton_getRegisterSize(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint32(triton::api.getRegisterSize());
      }


      static PyObject* triton_getSymbolicExpressionFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicExpressionFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getSymbolicExpressionFromId(): Expects an integer as argument.");

        try {
          return PySymbolicExpression(triton::api.getSymbolicExpressionFromId(PyLong_AsUsize(symExprId)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicExpressions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicExpressions(): Architecture is not defined.");

        try {
          const auto& expressions = triton::api.getSymbolicExpressions();

          ret = xPyDict_New();
          for (auto it = expressions.begin(); it != expressions.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getSymbolicMemory(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemory(): Architecture is not defined.");

        try {
          auto regs = triton::api.getSymbolicMemory();

          ret = xPyDict_New();
          for (auto it = regs.begin(); it != regs.end(); it++) {
            PyDict_SetItem(ret, PyLong_FromUint64(it->first), PySymbolicExpression(it->second));
          }
        }
        catch (const triton::exceptions::Exception& e) {
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
          return PyLong_FromUsize(triton::api.getSymbolicMemoryId(PyLong_AsUint64(addr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicMemoryValue(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryValue(): Architecture is not defined.");

        if (!PyLong_Check(mem) && !PyInt_Check(mem) && !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryValue(): Expects an integer or a MemoryAccess as argument.");

        try {
          if (PyLong_Check(mem) || PyInt_Check(mem))
            return PyLong_FromUint512(triton::api.getSymbolicMemoryValue(PyLong_AsUint64(mem)));
          return PyLong_FromUint512(triton::api.getSymbolicMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisters(): Architecture is not defined.");

        try {
          auto regs = triton::api.getSymbolicRegisters();

          ret = xPyDict_New();
          for (auto it = regs.begin(); it != regs.end(); it++) {
            triton::arch::Register reg(it->first);
            PyDict_SetItem(ret, PyRegister(reg), PySymbolicExpression(it->second));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getSymbolicRegisterId(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterId(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterId(): Expects a REG as argument.");

        try {
          return PyLong_FromUsize(triton::api.getSymbolicRegisterId(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicRegisterValue(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterValue(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterValue(): Expects a REG as argument.");

        try {
          return PyLong_FromUint512(triton::api.getSymbolicRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
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
          return PySymbolicVariable(triton::api.getSymbolicVariableFromId(PyLong_AsUsize(symVarId)));
        }
        catch (const triton::exceptions::Exception& e) {
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_getSymbolicVariables(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicVariables(): Architecture is not defined.");

        try {
          const auto& variables = triton::api.getSymbolicVariables();

          ret = xPyDict_New();
          for (auto it = variables.begin(); it != variables.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicVariable(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getTaintedMemory(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedMemory(): Architecture is not defined.");

        try {
          std::set<triton::uint64> addresses = triton::api.getTaintedMemory();

          size = addresses.size();
          ret = xPyList_New(size);
          for (auto it = addresses.begin(); it != addresses.end(); it++) {
            PyList_SetItem(ret, index, PyLong_FromUint64(*it));
            index++;
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getTaintedRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedRegisters(): Architecture is not defined.");

        try {
          std::set<triton::arch::Register> registers = triton::api.getTaintedRegisters();

          size = registers.size();
          ret = xPyList_New(size);
          for (auto it = registers.begin(); it != registers.end(); it++) {
            PyList_SetItem(ret, index, PyRegister(*it));
            index++;
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_getTaintedSymbolicExpressions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicExpressions(): Architecture is not defined.");

        try {
          auto expressions = triton::api.getTaintedSymbolicExpressions();

          size = expressions.size();
          ret = xPyList_New(size);
          for (auto it = expressions.begin(); it != expressions.end(); it++) {
            PyList_SetItem(ret, index, PySymbolicExpression(*it));
            index++;
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_isArchitectureValid(PyObject* self, PyObject* noarg) {
        if (triton::api.isArchitectureValid() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isFlag(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isFlag(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isFlag(): Expects a REG as argument.");

        if (triton::api.isFlag(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isMemoryMapped(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;
        triton::uint64 c_baseAddr = 0;
        triton::usize c_size      = 1;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &baseAddr, &size);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemoryMapped(): Architecture is not defined.");

        if (baseAddr == nullptr || (!PyLong_Check(baseAddr) && !PyInt_Check(baseAddr)))
          return PyErr_Format(PyExc_TypeError, "isMemoryMapped(): Expects a base address (integer) as first argument.");

        if (size != nullptr && !PyLong_Check(size) && !PyInt_Check(size))
          return PyErr_Format(PyExc_TypeError, "isMemoryMapped(): Expects a size (integer) as second argument.");

        try {
          c_baseAddr = PyLong_AsUint64(baseAddr);
          if (size != nullptr)
            c_size = PyLong_AsUsize(size);
          if (triton::api.isMemoryMapped(c_baseAddr, c_size) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_isMemorySymbolized(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemorySymbolized(): Architecture is not defined.");

        if (PyMemoryAccess_Check(mem)) {
          if (triton::api.isMemorySymbolized(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
        }

        else if (PyLong_Check(mem) || PyInt_Check(mem)) {
          if (triton::api.isMemorySymbolized(PyLong_AsUint64(mem)) == true)
            Py_RETURN_TRUE;
        }

        else
          return PyErr_Format(PyExc_TypeError, "isMemorySymbolized(): Expects a MemoryAccess or an integer as argument.");

        Py_RETURN_FALSE;
      }


      static PyObject* triton_isMemoryTainted(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemoryTainted(): Architecture is not defined.");

        if (PyMemoryAccess_Check(mem)) {
          if (triton::api.isMemoryTainted(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
        }

        else if (PyLong_Check(mem) || PyInt_Check(mem)) {
          if (triton::api.isMemoryTainted(PyLong_AsUint64(mem)) == true)
            Py_RETURN_TRUE;
        }

        else
          return PyErr_Format(PyExc_TypeError, "isMemoryTainted(): Expects a MemoryAccess or an integer as argument.");

        Py_RETURN_FALSE;
      }


      static PyObject* triton_isRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegister(): Expects a REG as argument.");

        if (triton::api.isRegister(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isRegisterSymbolized(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegisterSymbolized(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterSymbolized(): Expects a REG as argument.");

        if (triton::api.isRegisterSymbolized(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isRegisterTainted(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegisterTainted(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterTainted(): Expects a REG as argument.");

        if (triton::api.isRegisterTainted(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isRegisterValid(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegisterValid(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterValid(): Expects a REG as argument.");

        if (triton::api.isRegisterValid(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isSymbolicEngineEnabled(PyObject* self, PyObject* noarg) {
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isSymbolicEngineEnabled(): Architecture is not defined.");

        if (triton::api.isSymbolicEngineEnabled() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isSymbolicExpressionIdExists(PyObject* self, PyObject* symExprId) {
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Architecture is not defined.");

        if (!PyInt_Check(symExprId) && !PyLong_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Expects an integer as argument.");

        if (triton::api.isSymbolicExpressionIdExists(PyLong_AsUsize(symExprId)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isModeEnabled(PyObject* self, PyObject* mode) {
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isModeEnabled(): Architecture is not defined.");

        if (!PyInt_Check(mode) && !PyLong_Check(mode))
          return PyErr_Format(PyExc_TypeError, "isModeEnabled(): Expects a MODE as argument.");

        if (triton::api.isModeEnabled(static_cast<enum triton::modes::mode_e>(PyLong_AsUint32(mode))) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* triton_isTaintEngineEnabled(PyObject* self, PyObject* noarg) {
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isTaintEngineEnabled(): Architecture is not defined.");

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

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Expects a AstNode as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicExpression(triton::api.newSymbolicExpression(PyAstNode_AsAstNode(node), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
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
          return PySymbolicVariable(triton::api.newSymbolicVariable(PyLong_AsUint32(size), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
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
          if (triton::api.processing(*PyInstruction_AsInstruction(inst)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_removeAllCallbacks(PyObject* self, PyObject* noarg) {
        try {
          triton::api.removeAllCallbacks();
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_removeCallback(PyObject* self, PyObject* args) {
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &function, &mode);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Architecture is not defined.");

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Expects a CALLBACK as second argument.");

        try {
          switch (static_cast<triton::callbacks::callback_e>(PyLong_AsUint32(mode))) {
            case callbacks::GET_CONCRETE_MEMORY_VALUE:
              triton::api.removeCallback(callbacks::getConcreteMemoryValueCallback(nullptr, function));
              break;
            case callbacks::GET_CONCRETE_REGISTER_VALUE:
              triton::api.removeCallback(callbacks::getConcreteRegisterValueCallback(nullptr, function));
              break;
            case callbacks::SYMBOLIC_SIMPLIFICATION:
              triton::api.removeCallback(callbacks::symbolicSimplificationCallback(nullptr, function));
              break;
            default:
              return PyErr_Format(PyExc_TypeError, "removeCallback(): Invalid kind of callback.");
          }
        }
        catch (const triton::exceptions::Exception& e) {
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setArchitecture(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "setArchitecture(): Expects an ARCH as argument.");

        try {
          triton::api.setArchitecture(PyLong_AsUint32(arg));

        /* Update python env ======================================================== */
          triton::bindings::python::initRegNamespace();
          triton::bindings::python::initCpuSizeNamespace();
          triton::bindings::python::initX86OpcodesNamespace();
          triton::bindings::python::initX86PrefixesNamespace();
          #if defined(__unix__) || defined(__APPLE__)
            triton::bindings::python::initSyscallNamespace();
          #endif
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setAstRepresentationMode(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "setArcsetAstRepresentationMode(): Expects an AST_REPRESENTATION as argument.");

        try {
          triton::api.setAstRepresentationMode(PyLong_AsUint32(arg));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setConcreteMemoryAreaValue(PyObject* self, PyObject* args) {
        std::vector<triton::uint8> vv;
        PyObject* baseAddr  = nullptr;
        PyObject* values    = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &baseAddr, &values);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setConcreteMemoryAreaValue(): Architecture is not defined.");

        if (baseAddr == nullptr || (!PyLong_Check(baseAddr) && !PyInt_Check(baseAddr)))
          return PyErr_Format(PyExc_TypeError, "setConcreteMemoryAreaValue(): Expects an integer as first argument.");

        if (values == nullptr)
          return PyErr_Format(PyExc_TypeError, "setConcreteMemoryAreaValue(): Expects a list or bytes as second argument.");

        // Python object: List
        if (PyList_Check(values)) {
          for (Py_ssize_t i = 0; i < PyList_Size(values); i++) {
            PyObject* item = PyList_GetItem(values, i);

            if ((!PyLong_Check(item) && !PyInt_Check(item)) || PyLong_AsUint32(item) > 0xff)
              return PyErr_Format(PyExc_TypeError, "setConcreteMemoryAreaValue(): Each item of the list must be a 8-bits integer.");

            vv.push_back(static_cast<triton::uint8>(PyLong_AsUint32(item) & 0xff));
          }

          try {
            triton::api.setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), vv);
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        // Python object: Bytes
        else if (PyBytes_Check(values)) {
          triton::uint8* area = reinterpret_cast<triton::uint8*>(PyBytes_AsString(values));
          triton::usize  size = static_cast<triton::usize>(PyBytes_Size(values));

          try {
            triton::api.setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), area, size);
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        // Python object: ByteArray
        else if (PyByteArray_Check(values)) {
          triton::uint8* area = reinterpret_cast<triton::uint8*>(PyByteArray_AsString(values));
          triton::usize  size = static_cast<triton::usize>(PyByteArray_Size(values));

          try {
            triton::api.setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), area, size);
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        // Invalid Python object
        else
          return PyErr_Format(PyExc_TypeError, "setConcreteMemoryAreaValue(): Expects a list or bytes as second argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setConcreteMemoryValue(PyObject* self, PyObject* args) {
        PyObject* mem    = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &value);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Architecture is not defined.");

        /* setConcreteMemoryValue(integer, integer) */
        if (mem != nullptr && (PyLong_Check(mem) || PyInt_Check(mem))) {
          if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
            return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Expects a value as second argument.");

          triton::uint64 addr   = PyLong_AsUint64(mem);
          triton::uint32 cvalue = PyLong_AsUint32(value);

          if (cvalue > 0xff)
            return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Value must be on 8 bits.");

          try {
            triton::api.setConcreteMemoryValue(addr, static_cast<triton::uint8>(cvalue & 0xff));
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }

        }

        /* setConcreteMemoryValue(MemoryAccess) */
        else if (mem != nullptr && PyMemoryAccess_Check(mem)) {
          if (value != nullptr)
            return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Expects no second argument.");
          try {
            triton::api.setConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem));
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* Invalid */
        else
          return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Expects a MemoryAccess or an integer as first argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setConcreteRegisterValue(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setConcreteRegisterValue(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "setConcreteRegisterValue(): Expects a REG as first argument.");

        try {
          triton::api.setConcreteRegisterValue(*PyRegister_AsRegister(reg));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_setTaintMemory(PyObject* self, PyObject* args) {
        PyObject* mem    = nullptr;
        PyObject* flag   = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &flag);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setTaintMemory(): Architecture is not defined.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "setTaintMemory(): Expects a MemoryAccess as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTaintMemory(): Expects a boolean as second argument.");

        try {
          if (triton::api.setTaintMemory(*PyMemoryAccess_AsMemoryAccess(mem), PyLong_AsBool(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_setTaintRegister(PyObject* self, PyObject* args) {
        PyObject* reg    = nullptr;
        PyObject* flag   = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &flag);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setTaintRegister(): Architecture is not defined.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "setTaintRegister(): Expects a REG as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTaintRegister(): Expects a boolean as second argument.");

        try {
          if (triton::api.setTaintRegister(*PyRegister_AsRegister(reg), PyLong_AsBool(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_simplify(PyObject* self, PyObject* args) {
        PyObject* node        = nullptr;
        PyObject* z3Flag      = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &z3Flag);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "simplify(): Architecture is not defined.");

        if (node == nullptr || !PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "simplify(): Expects a AstNode as first argument.");

        if (z3Flag != nullptr && !PyBool_Check(z3Flag))
          return PyErr_Format(PyExc_TypeError, "simplify(): Expects a boolean as second argument.");

        if (z3Flag == nullptr)
          z3Flag = PyLong_FromUint32(false);

        try {
          return PyAstNode(triton::api.processSimplification(PyAstNode_AsAstNode(node), PyLong_AsBool(z3Flag)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_sliceExpressions(PyObject* self, PyObject* expr) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "sliceExpressions(): Architecture is not defined.");

        if (!PySymbolicExpression_Check(expr))
          return PyErr_Format(PyExc_TypeError, "sliceExpressions(): Expects a SymbolicExpression as argument.");

        try {
          auto exprs = triton::api.sliceExpressions(PySymbolicExpression_AsSymbolicExpression(expr));

          ret = xPyDict_New();
          for (auto it = exprs.begin(); it != exprs.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* triton_taintAssignmentMemoryImmediate(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryImmediate(): Architecture is not defined.");

        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryImmediate(): Expects a MemoryAccess as argument.");

        try {
          if (triton::api.taintAssignmentMemoryImmediate(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentMemoryMemory(PyObject* self, PyObject* args) {
        PyObject* mem1 = nullptr;
        PyObject* mem2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem1, &mem2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryMemory(): Architecture is not defined.");

        if (mem1 == nullptr || !PyMemoryAccess_Check(mem1))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryMemory(): Expects a MemoryAccess as first argument.");

        if (mem2 == nullptr || !PyMemoryAccess_Check(mem2))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (triton::api.taintAssignmentMemoryMemory(*PyMemoryAccess_AsMemoryAccess(mem1), *PyMemoryAccess_AsMemoryAccess(mem2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentMemoryRegister(PyObject* self, PyObject* args) {
        PyObject* mem = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &reg);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryRegister(): Architecture is not defined.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryRegister(): Expects a MemoryAccess as first argument.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryRegister(): Expects a REG as second argument.");

        try {
          if (triton::api.taintAssignmentMemoryRegister(*PyMemoryAccess_AsMemoryAccess(mem), *PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentRegisterImmediate(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterImmediate(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterImmediate(): Expects a REG as argument.");

        try {
          if (triton::api.taintAssignmentRegisterImmediate(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentRegisterMemory(PyObject* self, PyObject* args) {
        PyObject* reg = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &mem);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterMemory(): Architecture is not defined.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterMemory(): Expects a REG as first argument.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (triton::api.taintAssignmentRegisterMemory(*PyRegister_AsRegister(reg), *PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintAssignmentRegisterRegister(PyObject* self, PyObject* args) {
        PyObject* reg1 = nullptr;
        PyObject* reg2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg1, &reg2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterRegister(): Architecture is not defined.");

        if (reg1 == nullptr || !PyRegister_Check(reg1))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterRegister(): Expects a REG as first argument.");

        if (reg2 == nullptr || !PyRegister_Check(reg2))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterRegister(): Expects a REG as second argument.");

        try {
          if (triton::api.taintAssignmentRegisterRegister(*PyRegister_AsRegister(reg1), *PyRegister_AsRegister(reg2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintMemory(): Architecture is not defined.");

        try {
          if (PyMemoryAccess_Check(mem)) {
            if (triton::api.taintMemory(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
              Py_RETURN_TRUE;
          }

          else if (PyLong_Check(mem) || PyInt_Check(mem)) {
            if (triton::api.taintMemory(PyLong_AsUint64(mem)) == true)
              Py_RETURN_TRUE;
          }

          else
            return PyErr_Format(PyExc_TypeError, "taintMemory(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        Py_RETURN_FALSE;
      }


      static PyObject* triton_taintRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintRegister(): Expects a REG as argument.");

        try {
          if (triton::api.taintRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionMemoryImmediate(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryImmediate(): Architecture is not defined.");

        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryImmediate(): Expects a MemoryAccess as argument.");

        try {
          if (triton::api.taintUnionMemoryImmediate(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionMemoryMemory(PyObject* self, PyObject* args) {
        PyObject* mem1 = nullptr;
        PyObject* mem2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem1, &mem2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryMemory(): Architecture is not defined.");

        if (mem1 == nullptr || !PyMemoryAccess_Check(mem1))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryMemory(): Expects a MemoryAccess as first argument.");

        if (mem2 == nullptr || !PyMemoryAccess_Check(mem2))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (triton::api.taintUnionMemoryMemory(*PyMemoryAccess_AsMemoryAccess(mem1), *PyMemoryAccess_AsMemoryAccess(mem2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionMemoryRegister(PyObject* self, PyObject* args) {
        PyObject* mem = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &reg);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryRegister(): Architecture is not defined.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryRegister(): Expects a MemoryAccess as first argument.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryRegister(): Expects a REG as second argument.");

        try {
          if (triton::api.taintUnionMemoryRegister(*PyMemoryAccess_AsMemoryAccess(mem), *PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionRegisterImmediate(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterImmediate(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterImmediate(): Expects a REG as argument.");

        try {
          if (triton::api.taintUnionRegisterImmediate(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionRegisterMemory(PyObject* self, PyObject* args) {
        PyObject* reg = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &mem);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterMemory(): Architecture is not defined.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterMemory(): Expects a REG as first argument.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (triton::api.taintUnionRegisterMemory(*PyRegister_AsRegister(reg), *PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_taintUnionRegisterRegister(PyObject* self, PyObject* args) {
        PyObject* reg1 = nullptr;
        PyObject* reg2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg1, &reg2);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterRegister(): Architecture is not defined.");

        if (reg1 == nullptr || !PyRegister_Check(reg1))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterRegister(): Expects a REG as first argument.");

        if (reg2 == nullptr || !PyRegister_Check(reg2))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterRegister(): Expects a REG as second argument.");

        try {
          if (triton::api.taintUnionRegisterRegister(*PyRegister_AsRegister(reg1), *PyRegister_AsRegister(reg2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_unmapMemory(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;
        triton::uint64 c_baseAddr = 0;
        triton::usize c_size      = 1;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &baseAddr, &size);

        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "unmapMemory(): Architecture is not defined.");

        if (baseAddr == nullptr || (!PyLong_Check(baseAddr) && !PyInt_Check(baseAddr)))
          return PyErr_Format(PyExc_TypeError, "unmapMemory(): Expects a base address (integer) as first argument.");

        if (size != nullptr && !PyLong_Check(size) && !PyInt_Check(size))
          return PyErr_Format(PyExc_TypeError, "unmapMemory(): Expects a size (integer) as second argument.");

        try {
          c_baseAddr = PyLong_AsUint64(baseAddr);
          if (size != nullptr)
            c_size = PyLong_AsUsize(size);
          triton::api.unmapMemory(c_baseAddr, c_size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* triton_untaintMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintMemory(): Architecture is not defined.");

        try {
          if (PyMemoryAccess_Check(mem)) {
            if (triton::api.untaintMemory(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
              Py_RETURN_TRUE;
          }

          else if (PyLong_Check(mem) || PyInt_Check(mem)) {
            if (triton::api.untaintMemory(PyLong_AsUint64(mem)) == true)
              Py_RETURN_TRUE;
          }

          else
            return PyErr_Format(PyExc_TypeError, "untaintMemory(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        Py_RETURN_FALSE;
      }


      static PyObject* triton_untaintRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "untaintRegister(): Expects a REG as argument.");

        try {
          if (triton::api.untaintRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      PyMethodDef tritonCallbacks[] = {
        {"Elf",                                 (PyCFunction)triton_Elf,                                    METH_O,             ""},
        {"Immediate",                           (PyCFunction)triton_Immediate,                              METH_VARARGS,       ""},
        {"Instruction",                         (PyCFunction)triton_Instruction,                            METH_VARARGS,       ""},
        {"MemoryAccess",                        (PyCFunction)triton_MemoryAccess,                           METH_VARARGS,       ""},
        {"Pe",                                  (PyCFunction)triton_Pe,                                     METH_O,             ""},
        {"Register",                            (PyCFunction)triton_Register,                               METH_VARARGS,       ""},
        {"addCallback",                         (PyCFunction)triton_addCallback,                            METH_VARARGS,       ""},
        {"assignSymbolicExpressionToMemory",    (PyCFunction)triton_assignSymbolicExpressionToMemory,       METH_VARARGS,       ""},
        {"assignSymbolicExpressionToRegister",  (PyCFunction)triton_assignSymbolicExpressionToRegister,     METH_VARARGS,       ""},
        {"buildSemantics",                      (PyCFunction)triton_buildSemantics,                         METH_O,             ""},
        {"buildSymbolicImmediate",              (PyCFunction)triton_buildSymbolicImmediate,                 METH_O,             ""},
        {"buildSymbolicMemory",                 (PyCFunction)triton_buildSymbolicMemory,                    METH_O,             ""},
        {"buildSymbolicRegister",               (PyCFunction)triton_buildSymbolicRegister,                  METH_O,             ""},
        {"clearPathConstraints",                (PyCFunction)triton_clearPathConstraints,                   METH_NOARGS,        ""},
        {"concretizeAllMemory",                 (PyCFunction)triton_concretizeAllMemory,                    METH_NOARGS,        ""},
        {"concretizeAllRegister",               (PyCFunction)triton_concretizeAllRegister,                  METH_NOARGS,        ""},
        {"concretizeMemory",                    (PyCFunction)triton_concretizeMemory,                       METH_O,             ""},
        {"concretizeRegister",                  (PyCFunction)triton_concretizeRegister,                     METH_O,             ""},
        {"convertExpressionToSymbolicVariable", (PyCFunction)triton_convertExpressionToSymbolicVariable,    METH_VARARGS,       ""},
        {"convertMemoryToSymbolicVariable",     (PyCFunction)triton_convertMemoryToSymbolicVariable,        METH_VARARGS,       ""},
        {"convertRegisterToSymbolicVariable",   (PyCFunction)triton_convertRegisterToSymbolicVariable,      METH_VARARGS,       ""},
        {"createSymbolicFlagExpression",        (PyCFunction)triton_createSymbolicFlagExpression,           METH_VARARGS,       ""},
        {"createSymbolicMemoryExpression",      (PyCFunction)triton_createSymbolicMemoryExpression,         METH_VARARGS,       ""},
        {"createSymbolicRegisterExpression",    (PyCFunction)triton_createSymbolicRegisterExpression,       METH_VARARGS,       ""},
        {"createSymbolicVolatileExpression",    (PyCFunction)triton_createSymbolicVolatileExpression,       METH_VARARGS,       ""},
        {"disassembly",                         (PyCFunction)triton_disassembly,                            METH_O,             ""},
        {"enableMode",                          (PyCFunction)triton_enableMode,                             METH_VARARGS,       ""},
        {"enableSymbolicEngine",                (PyCFunction)triton_enableSymbolicEngine,                   METH_O,             ""},
        {"enableTaintEngine",                   (PyCFunction)triton_enableTaintEngine,                      METH_O,             ""},
        {"evaluateAstViaZ3",                    (PyCFunction)triton_evaluateAstViaZ3,                       METH_O,             ""},
        {"getAllRegisters",                     (PyCFunction)triton_getAllRegisters,                        METH_NOARGS,        ""},
        {"getArchitecture",                     (PyCFunction)triton_getArchitecture,                        METH_NOARGS,        ""},
        {"getAstDictionariesStats",             (PyCFunction)triton_getAstDictionariesStats,                METH_NOARGS,        ""},
        {"getAstFromId",                        (PyCFunction)triton_getAstFromId,                           METH_O,             ""},
        {"getAstRepresentationMode",            (PyCFunction)triton_getAstRepresentationMode,               METH_NOARGS,        ""},
        {"getConcreteMemoryAreaValue",          (PyCFunction)triton_getConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"getConcreteMemoryValue",              (PyCFunction)triton_getConcreteMemoryValue,                 METH_O,             ""},
        {"getConcreteRegisterValue",            (PyCFunction)triton_getConcreteRegisterValue,               METH_O,             ""},
        {"getFullAst",                          (PyCFunction)triton_getFullAst,                             METH_O,             ""},
        {"getFullAstFromId",                    (PyCFunction)triton_getFullAstFromId,                       METH_O,             ""},
        {"getModel",                            (PyCFunction)triton_getModel,                               METH_O,             ""},
        {"getModels",                           (PyCFunction)triton_getModels,                              METH_VARARGS,       ""},
        {"getParentRegisters",                  (PyCFunction)triton_getParentRegisters,                     METH_NOARGS,        ""},
        {"getPathConstraints",                  (PyCFunction)triton_getPathConstraints,                     METH_NOARGS,        ""},
        {"getPathConstraintsAst",               (PyCFunction)triton_getPathConstraintsAst,                  METH_NOARGS,        ""},
        {"getRegisterBitSize",                  (PyCFunction)triton_getRegisterBitSize,                     METH_NOARGS,        ""},
        {"getRegisterSize",                     (PyCFunction)triton_getRegisterSize,                        METH_NOARGS,        ""},
        {"getSymbolicExpressionFromId",         (PyCFunction)triton_getSymbolicExpressionFromId,            METH_O,             ""},
        {"getSymbolicExpressions",              (PyCFunction)triton_getSymbolicExpressions,                 METH_NOARGS,        ""},
        {"getSymbolicMemory",                   (PyCFunction)triton_getSymbolicMemory,                      METH_NOARGS,        ""},
        {"getSymbolicMemoryId",                 (PyCFunction)triton_getSymbolicMemoryId,                    METH_O,             ""},
        {"getSymbolicMemoryValue",              (PyCFunction)triton_getSymbolicMemoryValue,                 METH_O,             ""},
        {"getSymbolicRegisterId",               (PyCFunction)triton_getSymbolicRegisterId,                  METH_O,             ""},
        {"getSymbolicRegisterValue",            (PyCFunction)triton_getSymbolicRegisterValue,               METH_O,             ""},
        {"getSymbolicRegisters",                (PyCFunction)triton_getSymbolicRegisters,                   METH_NOARGS,        ""},
        {"getSymbolicVariableFromId",           (PyCFunction)triton_getSymbolicVariableFromId,              METH_O,             ""},
        {"getSymbolicVariableFromName",         (PyCFunction)triton_getSymbolicVariableFromName,            METH_O,             ""},
        {"getSymbolicVariables",                (PyCFunction)triton_getSymbolicVariables,                   METH_NOARGS,        ""},
        {"getTaintedMemory",                    (PyCFunction)triton_getTaintedMemory,                       METH_NOARGS,        ""},
        {"getTaintedRegisters",                 (PyCFunction)triton_getTaintedRegisters,                    METH_NOARGS,        ""},
        {"getTaintedSymbolicExpressions",       (PyCFunction)triton_getTaintedSymbolicExpressions,          METH_NOARGS,        ""},
        {"isArchitectureValid",                 (PyCFunction)triton_isArchitectureValid,                    METH_NOARGS,        ""},
        {"isFlag",                              (PyCFunction)triton_isFlag,                                 METH_O,             ""},
        {"isMemoryMapped",                      (PyCFunction)triton_isMemoryMapped,                         METH_VARARGS,       ""},
        {"isMemorySymbolized",                  (PyCFunction)triton_isMemorySymbolized,                     METH_O,             ""},
        {"isMemoryTainted",                     (PyCFunction)triton_isMemoryTainted,                        METH_O,             ""},
        {"isModeEnabled",                       (PyCFunction)triton_isModeEnabled,                          METH_O,             ""},
        {"isRegister",                          (PyCFunction)triton_isRegister,                             METH_O,             ""},
        {"isRegisterSymbolized",                (PyCFunction)triton_isRegisterSymbolized,                   METH_O,             ""},
        {"isRegisterTainted",                   (PyCFunction)triton_isRegisterTainted,                      METH_O,             ""},
        {"isRegisterValid",                     (PyCFunction)triton_isRegisterValid,                        METH_O,             ""},
        {"isSymbolicEngineEnabled",             (PyCFunction)triton_isSymbolicEngineEnabled,                METH_NOARGS,        ""},
        {"isSymbolicExpressionIdExists",        (PyCFunction)triton_isSymbolicExpressionIdExists,           METH_O,             ""},
        {"isTaintEngineEnabled",                (PyCFunction)triton_isTaintEngineEnabled,                   METH_NOARGS,        ""},
        {"newSymbolicExpression",               (PyCFunction)triton_newSymbolicExpression,                  METH_VARARGS,       ""},
        {"newSymbolicVariable",                 (PyCFunction)triton_newSymbolicVariable,                    METH_VARARGS,       ""},
        {"processing",                          (PyCFunction)triton_processing,                             METH_O,             ""},
        {"removeAllCallbacks",                  (PyCFunction)triton_removeAllCallbacks,                     METH_NOARGS,        ""},
        {"removeCallback",                      (PyCFunction)triton_removeCallback,                         METH_VARARGS,       ""},
        {"resetEngines",                        (PyCFunction)triton_resetEngines,                           METH_NOARGS,        ""},
        {"setArchitecture",                     (PyCFunction)triton_setArchitecture,                        METH_O,             ""},
        {"setAstRepresentationMode",            (PyCFunction)triton_setAstRepresentationMode,               METH_O,             ""},
        {"setConcreteMemoryAreaValue",          (PyCFunction)triton_setConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"setConcreteMemoryValue",              (PyCFunction)triton_setConcreteMemoryValue,                 METH_VARARGS,       ""},
        {"setConcreteRegisterValue",            (PyCFunction)triton_setConcreteRegisterValue,               METH_O,             ""},
        {"setTaintMemory",                      (PyCFunction)triton_setTaintMemory,                         METH_VARARGS,       ""},
        {"setTaintRegister",                    (PyCFunction)triton_setTaintRegister,                       METH_VARARGS,       ""},
        {"simplify",                            (PyCFunction)triton_simplify,                               METH_VARARGS,       ""},
        {"sliceExpressions",                    (PyCFunction)triton_sliceExpressions,                       METH_O,             ""},
        {"taintAssignmentMemoryImmediate",      (PyCFunction)triton_taintAssignmentMemoryImmediate,         METH_O,             ""},
        {"taintAssignmentMemoryMemory",         (PyCFunction)triton_taintAssignmentMemoryMemory,            METH_VARARGS,       ""},
        {"taintAssignmentMemoryRegister",       (PyCFunction)triton_taintAssignmentMemoryRegister,          METH_VARARGS,       ""},
        {"taintAssignmentRegisterImmediate",    (PyCFunction)triton_taintAssignmentRegisterImmediate,       METH_O,             ""},
        {"taintAssignmentRegisterMemory",       (PyCFunction)triton_taintAssignmentRegisterMemory,          METH_VARARGS,       ""},
        {"taintAssignmentRegisterRegister",     (PyCFunction)triton_taintAssignmentRegisterRegister,        METH_VARARGS,       ""},
        {"taintMemory",                         (PyCFunction)triton_taintMemory,                            METH_O,             ""},
        {"taintRegister",                       (PyCFunction)triton_taintRegister,                          METH_O,             ""},
        {"taintUnionMemoryImmediate",           (PyCFunction)triton_taintUnionMemoryImmediate,              METH_O,             ""},
        {"taintUnionMemoryMemory",              (PyCFunction)triton_taintUnionMemoryMemory,                 METH_VARARGS,       ""},
        {"taintUnionMemoryRegister",            (PyCFunction)triton_taintUnionMemoryRegister,               METH_VARARGS,       ""},
        {"taintUnionRegisterImmediate",         (PyCFunction)triton_taintUnionRegisterImmediate,            METH_O,             ""},
        {"taintUnionRegisterMemory",            (PyCFunction)triton_taintUnionRegisterMemory,               METH_VARARGS,       ""},
        {"taintUnionRegisterRegister",          (PyCFunction)triton_taintUnionRegisterRegister,             METH_VARARGS,       ""},
        {"unmapMemory",                         (PyCFunction)triton_unmapMemory,                            METH_VARARGS,       ""},
        {"untaintMemory",                       (PyCFunction)triton_untaintMemory,                          METH_O,             ""},
        {"untaintRegister",                     (PyCFunction)triton_untaintRegister,                        METH_O,             ""},
        {nullptr,                               nullptr,                                                    0,                  nullptr}

      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

