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

- <b>\ref py_SymbolicVariable_page convertExpressionToSymbolicVariable(integer symExprId, integer symVarSize, string comment="")</b><br>
Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page convertMemoryToSymbolicVariable(\ref py_MemoryAccess_page mem, string comment="")</b><br>
Converts a symbolic memory expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page convertRegisterToSymbolicVariable(\ref py_REG_page reg, string comment="")</b><br>
Converts a symbolic register expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicExpression_page createSymbolicFlagExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_REG_page flag, string comment="")</b><br>
Returns the new symbolic register expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicMemoryExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_MemoryAccess_page mem, string comment="")</b><br>
Returns the new symbolic memory expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicRegisterExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_REG_page reg, string comment="")</b><br>
Returns the new symbolic register expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicVolatileExpression (\ref py_Instruction_page inst, \ref py_AstNode_page node, string comment="")</b><br>
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

- <b>[dict, ...] getModels(\ref py_AstNode_page node)</b><br>
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

- <b>\ref py_SymbolicExpression_page newSymbolicExpression(\ref py_AstNode_page node, string comment="")</b><br>
Returns a new symbolic expression. Note that if there are simplification passes recorded, simplifications will be applied.

- <b>\ref py_SymbolicVariable_page newSymbolicVariable(intger varSize, string comment="")</b><br>
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
          return PyErr_Format(PyExc_TypeError, "Instruction(): Expected a bytes array as argument.");

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

      static PyObject* triton_TritonContext(PyObject* self, PyObject* args) {
        return PyTritonContext();
      }


      PyMethodDef tritonCallbacks[] = {
        {"TritonContext",                       (PyCFunction)triton_TritonContext,                          METH_VARARGS,       ""},
        {"Elf",                                 (PyCFunction)triton_Elf,                                    METH_O,             ""},
        {"Immediate",                           (PyCFunction)triton_Immediate,                              METH_VARARGS,       ""},
        {"Instruction",                         (PyCFunction)triton_Instruction,                            METH_VARARGS,       ""},
        {"MemoryAccess",                        (PyCFunction)triton_MemoryAccess,                           METH_VARARGS,       ""},
        {"Pe",                                  (PyCFunction)triton_Pe,                                     METH_O,             ""},
        {nullptr,                               nullptr,                                                    0,                  nullptr}

      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

