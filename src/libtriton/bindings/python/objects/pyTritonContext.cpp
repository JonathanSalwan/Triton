//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/api.hpp>
#include <triton/arm32Cpu.hpp>
#include <triton/exceptions.hpp>
#include <triton/register.hpp>



/*! \page py_TritonContext_page TritonContext
    \brief [**python api**] All information about the Triton Context class
    \anchor tritonContext

\section triton_py_description Description
<hr>

libTriton offers Python bindings on top of its C++ API which allow you to build analysis in Python as well as in C++.

~~~~~~~~~~~~~{.py}
>>> from triton import TritonContext, ARCH
>>>
>>> ctx1 = TritonContext()
>>> ctx1.setArchitecture(ARCH.X86_64)
>>>
>>> ctx2 = TritonContext(ARCH.AARCH64)

~~~~~~~~~~~~~

\section tritonContext_py_api Python API - Methods of the TritonContext class
<hr>

\subsection TritonContext_py_api_methods Methods

- <b>void addCallback(function cb, \ref py_CALLBACK_page kind)</b><br>
Adds a callback at specific internal points. Your callback will be called each time the point is reached.

- <b>void assignSymbolicExpressionToMemory(\ref py_SymbolicExpression_page symExpr, \ref py_MemoryAccess_page mem)</b><br>
Assigns a \ref py_SymbolicExpression_page to a \ref py_MemoryAccess_page area. **Be careful**, use this function only if you know what you are doing.
The symbolic expression (`symExpr`) must be aligned to the memory access.

- <b>void assignSymbolicExpressionToRegister(\ref py_SymbolicExpression_page symExpr, \ref py_Register_page reg)</b><br>
Assigns a \ref py_SymbolicExpression_page to a \ref py_Register_page. **Be careful**, use this function only if you know what you are doing.
The symbolic expression (`symExpr`) must be aligned to the targeted size register. The register must be a parent register.

- <b>bool buildSemantics(\ref py_Instruction_page inst)</b><br>
Builds the instruction semantics. Returns true if the instruction is supported. You must define an architecture before.

- <b>void clearCallbacks(void)</b><br>
Clears recorded callbacks.

- <b>void clearModes(void)</b><br>
Clears recorded modes.

- <b>void clearConcreteMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Clears concrete values assigned to the memory cells.

- <b>void clearConcreteMemoryValue(integer addr, integer size)</b><br>
Clears concrete values assigned to the memory cells from `addr` to `addr + size`.

- <b>void clearPathConstraints(integer tid=0)</b><br>
Clears the current path predicate of a thread id.

- <b>void concretizeAllMemory(void)</b><br>
Concretizes all symbolic memory references.

- <b>void concretizeAllRegister(void)</b><br>
Concretizes all symbolic register references.

- <b>void concretizeMemory(integer addr)</b><br>
Concretizes a specific symbolic memory reference.

- <b>void concretizeMemory(\ref py_MemoryAccess_page mem)</b><br>
Concretizes a specific symbolic memory reference.

- <b>void concretizeRegister(\ref py_Register_page reg)</b><br>
Concretizes a specific symbolic register reference.

- <b>\ref py_SymbolicExpression_page createSymbolicMemoryExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_MemoryAccess_page mem, string comment)</b><br>
Returns the new symbolic memory expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicRegisterExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_Register_page reg, string comment)</b><br>
Returns the new symbolic register expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicVolatileExpression (\ref py_Instruction_page inst, \ref py_AstNode_page node, string comment)</b><br>
Returns the new symbolic volatile expression and links this expression to the instruction.

- <b>void disassembly(\ref py_Instruction_page inst)</b><br>
Disassembles the instruction and sets up operands. You must define an architecture before.

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

- <b>\ref py_AstContext_page getAstContext(void)</b><br>
Returns the AST context to create and modify nodes.

- <b>\ref py_AST_REPRESENTATION_page getAstRepresentationMode(void)</b><br>
Returns the current AST representation mode.

- <b>bytes getConcreteMemoryAreaValue(integer baseAddr, integer size)</b><br>
Returns the concrete value of a memory area.

- <b>integer getConcreteMemoryValue(integer addr)</b><br>
Returns the concrete value of a memory cell.

- <b>integer getConcreteMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the concrete value of memory cells.

- <b>integer getConcreteRegisterValue(\ref py_Register_page reg)</b><br>
Returns the concrete value of a register.

- <b>integer getConcreteVariableValue(\ref py_SymbolicVariable_page symVar)</b><br>
Returns the concrete value of a symbolic variable.

- <b>integer getGprBitSize(void)</b><br>
Returns the size in bits of the General Purpose Registers.

- <b>integer getGprSize(void)</b><br>
Returns the size in bytes of the General Purpose Registers.

- <b>\ref py_AstNode_page getImmediateAst(\ref py_Immediate_page imm)</b><br>
Returns the AST corresponding to the \ref py_Immediate_page.

- <b>\ref py_AstNode_page getMemoryAst(\ref py_MemoryAccess_page mem)</b><br>
Returns the AST corresponding to the \ref py_MemoryAccess_page with the SSA form.

- <b>dict getModel(\ref py_AstNode_page node)</b><br>
Computes and returns a model as a dictionary of {integer symVarId : \ref py_SolverModel_page model} from a symbolic constraint.

- <b>[dict, ...] getModels(\ref py_AstNode_page node, integer limit)</b><br>
Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.

- <b>\ref py_Register_page getParentRegister(\ref py_Register_page reg)</b><br>
Returns the parent \ref py_Register_page from a \ref py_Register_page.

- <b>[\ref py_Register_page, ...] getParentRegisters(void)</b><br>
Returns the list of parent registers. Each item of this list is a \ref py_Register_page.

- <b>[\ref py_PathConstraint_page, ...] getPathConstraints(integer tid=0)</b><br>
Returns the logical conjunction vector of path constraints of a thread id as a list of \ref py_PathConstraint_page.

- <b>\ref py_AstNode_page getPathPredicate(integer tid=0)</b><br>
Returns the current path predicate of a thread id as an AST of logical conjunction of each taken branch.

- <b>[\ref py_AstNode_page, ...] getPredicatesToReachAddress(integer addr, integer tid=0)</b><br>
Returns path predicates of a thread id which may reach the targeted address.

- <b>\ref py_Register_page getRegister(\ref py_REG_page id)</b><br>
Returns the \ref py_Register_page class corresponding to a \ref py_REG_page id.

- <b>\ref py_AstNode_page getRegisterAst(\ref py_Register_page reg)</b><br>
Returns the AST corresponding to the \ref py_Register_page with the SSA form.

- <b>\ref py_SymbolicExpression_page getSymbolicExpression(integer symExprId)</b><br>
Returns the symbolic expression corresponding to an id.

- <b>dict getSymbolicExpressions(void)</b><br>
Returns all symbolic expressions as a dictionary of {integer SymExprId : \ref py_SymbolicExpression_page expr}.

- <b>dict getSymbolicMemory(void)</b><br>
Returns the map of symbolic memory as {integer address : \ref py_SymbolicExpression_page expr}.

- <b>\ref py_SymbolicExpression_page getSymbolicMemory(integer addr)</b><br>
Returns the \ref py_SymbolicExpression_page corresponding to a memory address.

- <b>integer getSymbolicMemoryValue(integer addr)</b><br>
Returns the symbolic memory value.

- <b>integer getSymbolicMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the symbolic memory value.

- <b>dict getSymbolicRegisters(void)</b><br>
Returns the map of symbolic registers as {\ref py_REG_page reg : \ref py_SymbolicExpression_page expr}.

- <b>\ref py_SymbolicExpression_page getSymbolicRegister(\ref py_Register_page reg)</b><br>
Returns the \ref py_SymbolicExpression_page corresponding to the parent register.

- <b>integer getSymbolicRegisterValue(\ref py_Register_page reg)</b><br>
Returns the symbolic register value.

- <b>\ref py_SymbolicVariable_page getSymbolicVariable(integer symVarId)</b><br>
Returns the symbolic variable corresponding to a symbolic variable id.

- <b>\ref py_SymbolicVariable_page getSymbolicVariable(string symVarName)</b><br>
Returns the symbolic variable corresponding to a symbolic variable name.

- <b>dict getSymbolicVariables(void)</b><br>
Returns all symbolic variables as a dictionary of {integer SymVarId : \ref py_SymbolicVariable_page var}.

- <b>[integer, ...] getTaintedMemory(void)</b><br>
Returns the list of all tainted addresses.

- <b>[\ref py_Register_page, ...] getTaintedRegisters(void)</b><br>
Returns the list of all tainted registers.

- <b>[\ref py_SymbolicExpression_page, ...] getTaintedSymbolicExpressions(void)</b><br>
Returns the list of all tainted symbolic expressions.

- <b>bool isArchitectureValid(void)</b><br>
Returns true if the architecture is valid.

- <b>bool isConcreteMemoryValueDefined(\ref py_MemoryAccess_page mem)</b><br>
Returns true if memory cells have a defined concrete value.

- <b>bool isConcreteMemoryValueDefined(integer addr, integer size)</b><br>
Returns true if memory cells have a defined concrete value.

- <b>bool isFlag(\ref py_Register_page reg)</b><br>
Returns true if the register is a flag.

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

- <b>bool isRegister(\ref py_Register_page reg)</b><br>
Returns true if the register is a register (see also isFlag()).

- <b>bool isRegisterSymbolized(\ref py_Register_page reg)</b><br>
Returns true if the register expression contains a symbolic variable.

- <b>bool isRegisterTainted(\ref py_Register_page reg)</b><br>
Returns true if the register is tainted.

- <b>bool isRegisterValid(\ref py_Register_page reg)</b><br>
Returns true if the register is valid.

- <b>bool isSat(\ref py_AstNode_page node)</b><br>
Returns true if an expression is satisfiable.

- <b>bool isSymbolicEngineEnabled(void)</b><br>
Returns true if the symbolic execution engine is enabled.

- <b>bool isSymbolicExpressionExists(integer symExprId)</b><br>
Returns true if the symbolic expression id exists.

- <b>bool isTaintEngineEnabled(void)</b><br>
Returns true if the taint engine is enabled.

- <b>bool isThumb(void)</b><br>
Returns true if execution mode is Thumb (only valid for ARM32).

- <b>\ref py_SymbolicExpression_page newSymbolicExpression(\ref py_AstNode_page node, string comment)</b><br>
Returns a new symbolic expression. Note that if there are simplification passes recorded, simplifications will be applied.

- <b>\ref py_SymbolicVariable_page newSymbolicVariable(integer varSize, string alias)</b><br>
Returns a new symbolic variable.

- <b>void popPathConstraint(integer tid=0)</b><br>
Pops the last constraints added to the path predicate of a thread id.

- <b>void printSlicedExpressions(\ref py_SymbolicExpression_page expr, bool assert_=False)</b><br>
Prints symbolic expression with used references and symbolic variables in AST representation mode. If `assert_` is true, then (assert <expr>).

- <b>bool processing(\ref py_Instruction_page inst)</b><br>
Processes an instruction and updates engines according to the instruction semantics. Returns true if the instruction is supported. You must define an architecture before.

- <b>void pushPathConstraint(\ref py_AstNode_page node, integer tid=0)</b><br>
Pushs constraints to the current path predicate of a thread id.

- <b>void removeCallback(function cb, \ref py_CALLBACK_page kind)</b><br>
Removes a recorded callback.

- <b>void reset(void)</b><br>
Resets everything.

- <b>void setArchitecture(\ref py_ARCH_page arch)</b><br>
Initializes an architecture. This function must be called before any call to the rest of the API.

- <b>void setAstRepresentationMode(\ref py_AST_REPRESENTATION_page mode)</b><br>
Sets the AST representation mode.

- <b>void setConcreteMemoryAreaValue(integer baseAddr, [integer,])</b><br>
Sets the concrete value of a memory area. Note that setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteMemoryAreaValue(integer baseAddr, bytes opcodes)</b><br>
Sets the concrete value of a memory area. Note that setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteMemoryValue(integer addr, integer value)</b><br>
Sets the concrete value of a memory cell. Note that setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteMemoryValue(\ref py_MemoryAccess_page mem, integer value)</b><br>
Sets the concrete value of memory cells. Note that setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteRegisterValue(\ref py_Register_page reg, integer value)</b><br>
Sets the concrete value of a register. Note that setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteVariableValue(\ref py_SymbolicVariable_page symVar, integer value)</b><br>
Sets the concrete value of a symbolic variable.

- <b>void setMode(\ref py_MODE_page mode, bool flag)</b><br>
Enables or disables a specific mode.

- <b>bool setTaintMemory(\ref py_MemoryAccess_page mem, bool flag)</b><br>
Sets the targeted memory as tainted or not. Returns true if the memory is still tainted.

- <b>bool setTaintRegister(\ref py_Register_page reg, bool flag)</b><br>
Sets the targeted register as tainted or not. Returns true if the register is still tainted.

- <b>void setThumb(bool state)</b><br>
Sets CPU state to Thumb mode (only valid for ARM32).

- <b>\ref py_AstNode_page simplify(\ref py_AstNode_page node, bool z3=False)</b><br>
Calls all simplification callbacks recorded and returns a new simplified node. If the `z3` flag is
set to True, Triton will use z3 to simplify the given `node` before calling its recorded callbacks.

- <b>dict sliceExpressions(\ref py_SymbolicExpression_page expr)</b><br>
Slices expressions from a given one (backward slicing) and returns all symbolic expressions as a dictionary of {integer SymExprId : \ref py_SymbolicExpression_page expr}.

- <b>\ref py_SymbolicVariable_page symbolizeExpression(integer symExprId, integer symVarSize, string symVarAlias)</b><br>
Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page symbolizeMemory(\ref py_MemoryAccess_page mem, string symVarAlias)</b><br>
Converts a symbolic memory expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page symbolizeRegister(\ref py_Register_page reg, string symVarAlias)</b><br>
Converts a symbolic register expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>bool taintAssignment(\ref py_MemoryAccess_page memDst, \ref py_Immediate_page immSrc)</b><br>
Taints `memDst` from `immSrc` with an assignment - `memDst` is untained. Returns true if the `memDst` is still tainted.

- <b>bool taintAssignment(\ref py_MemoryAccess_page memDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an assignment - `memDst` is tainted if `memSrc` is tainted, otherwise
`memDst` is untained. Returns true if `memDst` is tainted.

- <b>bool taintAssignment(\ref py_MemoryAccess_page memDst, \ref py_Register_page regSrc)</b><br>
Taints `memDst` from `regSrc` with an assignment - `memDst` is tainted if `regSrc` is tainted, otherwise
`memDst` is untained. Return true if `memDst` is tainted.

- <b>bool taintAssignment(\ref py_Register_page regDst, \ref py_Immediate_page immSrc)</b><br>
Taints `regDst` from `immSrc` with an assignment - `regDst` is untained. Returns true if `reDst` is still tainted.

- <b>bool taintAssignment(\ref py_Register_page regDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `regDst` from `MemSrc` with an assignment - `regDst` is tainted if `memSrc` is tainted, otherwise
`regDst` is untained. Return true if `regDst` is tainted.

- <b>bool taintAssignment(\ref py_Register_page regDst, \ref py_Register_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an assignment - `regDst` is tainted if `regSrc` is tainted, otherwise
`regDst` is untained. Return true if `regDst` is tainted.

- <b>bool taintMemory(integer addr)</b><br>
Taints an address. Returns true if the address is tainted.

- <b>bool taintMemory(\ref py_MemoryAccess_page mem)</b><br>
Taints a memory. Returns true if the memory is tainted.

- <b>bool taintRegister(\ref py_Register_page reg)</b><br>
Taints a register. Returns true if the register is tainted.

- <b>bool taintUnion(\ref py_MemoryAccess_page memDst, \ref py_Immediate_page immSrc)</b><br>
Taints `memDst` from `immSrc` with an union - `memDst` does not changes. Returns true if `memDst` is tainted.

- <b>bool taintUnion(\ref py_MemoryAccess_page memDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an union - `memDst` is tainted if `memDst` or `memSrc` are
tainted. Returns true if `memDst` is tainted.

- <b>bool taintUnion(\ref py_MemoryAccess_page memDst, \ref py_Register_page regSrc)</b><br>
Taints `memDst` from `RegSrc` with an union - `memDst` is tainted if `memDst` or `regSrc` are
tainted. Returns true if `memDst` is tainted.

- <b>bool taintUnion(\ref py_Register_page regDst, \ref py_Immediate_page immSrc)</b><br>
Taints `regDst` from `immSrc` with an union - `regDst` does not changes. Returns true if `regDst` is tainted.

- <b>bool taintUnion(\ref py_Register_page regDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `regDst` from `memSrc` with an union - `regDst` is tainted if `regDst` or `memSrc` are
tainted. Returns true if `regDst` is tainted.

- <b>bool taintUnion(\ref py_Register_page regDst, \ref py_Register_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an union - `regDst` is tainted if `regDst` or `regSrc` are
tainted. Returns true if `regDst` is tainted.

- <b>bool untaintMemory(integer addr)</b><br>
Untaints an address. Returns true if the address is still tainted.

- <b>bool untaintMemory(\ref py_MemoryAccess_page mem)</b><br>
Untaints a memory. Returns true if the memory is still tainted.

- <b>bool untaintRegister(\ref py_Register_page reg)</b><br>
Untaints a register. Returns true if the register is still tainted.

*/



namespace triton {
  namespace bindings {
    namespace python {

      static void TritonContext_dealloc(PyObject* self) {
        if (((TritonContext_Object*)self)->ref == false)
          delete PyTritonContext_AsTritonContext(self);
        Py_XDECREF(((TritonContext_Object*)self)->regAttr);
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static void TritonContext_fillRegistersAttribute(PyObject* self) {
        /* Fill self->regAttr */
        auto& regs = PyTritonContext_AsTritonContext(self)->getAllRegisters();

        PyObject* registersDict = xPyDict_New();
        for (auto& reg : regs)
          xPyDict_SetItem(registersDict, xPyString_FromString(reg.second.getName().c_str()), PyRegister(reg.second));

        Py_XDECREF(((TritonContext_Object*)(self))->regAttr);
        ((TritonContext_Object*)(self))->regAttr = xPyClass_New(nullptr, registersDict, xPyString_FromString("registers"));
      }


      static PyObject* TritonContext_addCallback(PyObject* self, PyObject* args) {
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;
        PyObject* cb       = nullptr;
        PyObject* cb_self  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &function, &mode) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::addCallback(): Invalid number of arguments");
        }

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "TritonContext::addCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::addCallback(): Expects a CALLBACK as second argument.");

        if (PyMethod_Check(function)) {
          cb_self = PyMethod_GET_SELF(function);
          cb = PyMethod_GET_FUNCTION(function);
        }
        else {
          cb = function;
        }

        try {
          switch (static_cast<triton::callbacks::callback_e>(PyLong_AsUint32(mode))) {

            case callbacks::GET_CONCRETE_MEMORY_VALUE:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::getConcreteMemoryValueCallback([cb_self, cb](triton::API& api, const triton::arch::MemoryAccess& mem) {
                /********* Lambda *********/
                PyObject* args = nullptr;

                /* Create function args */
                if (cb_self) {
                  args = triton::bindings::python::xPyTuple_New(3);
                  PyTuple_SetItem(args, 0, cb_self);
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyMemoryAccess(mem));
                  Py_INCREF(cb_self);
                }
                else {
                  args = triton::bindings::python::xPyTuple_New(2);
                  PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyMemoryAccess(mem));
                }

                /* Call the callback */
                Py_INCREF(cb);
                PyObject* ret = PyObject_CallObject(cb, args);

                /* Check the call */
                if (ret == nullptr) {
                  throw triton::exceptions::PyCallbacks();
                }

                Py_DECREF(args);
                /********* End of lambda *********/
              }, cb));
              break;

            case callbacks::GET_CONCRETE_REGISTER_VALUE:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::getConcreteRegisterValueCallback([cb_self, cb](triton::API& api, const triton::arch::Register& reg){
                /********* Lambda *********/
                PyObject* args = nullptr;

                /* Create function args */
                if (cb_self) {
                  args = triton::bindings::python::xPyTuple_New(3);
                  PyTuple_SetItem(args, 0, cb_self);
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyRegister(reg));
                  Py_INCREF(cb_self);
                }
                else {
                  args = triton::bindings::python::xPyTuple_New(2);
                  PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyRegister(reg));
                }

                /* Call the callback */
                Py_INCREF(cb);
                PyObject* ret = PyObject_CallObject(cb, args);

                /* Check the call */
                if (ret == nullptr) {
                  throw triton::exceptions::PyCallbacks();
                }

                Py_DECREF(args);
                /********* End of lambda *********/
              }, cb));
              break;

            case callbacks::SET_CONCRETE_MEMORY_VALUE:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::setConcreteMemoryValueCallback([cb_self, cb](triton::API& api, const triton::arch::MemoryAccess& mem, const triton::uint512& value) {
                /********* Lambda *********/
                PyObject* args = nullptr;

                /* Create function args */
                if (cb_self) {
                  args = triton::bindings::python::xPyTuple_New(4);
                  PyTuple_SetItem(args, 0, cb_self);
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyMemoryAccess(mem));
                  PyTuple_SetItem(args, 3, triton::bindings::python::PyLong_FromUint512(value));
                  Py_INCREF(cb_self);
                }
                else {
                  args = triton::bindings::python::xPyTuple_New(3);
                  PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyMemoryAccess(mem));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyLong_FromUint512(value));
                }

                /* Call the callback */
                Py_INCREF(cb);
                PyObject* ret = PyObject_CallObject(cb, args);

                /* Check the call */
                if (ret == nullptr) {
                  throw triton::exceptions::PyCallbacks();
                }

                Py_DECREF(args);
                /********* End of lambda *********/
              }, cb));
              break;

            case callbacks::SET_CONCRETE_REGISTER_VALUE:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::setConcreteRegisterValueCallback([cb_self, cb](triton::API& api, const triton::arch::Register& reg, const triton::uint512& value){
                /********* Lambda *********/
                PyObject* args = nullptr;

                /* Create function args */
                if (cb_self) {
                  args = triton::bindings::python::xPyTuple_New(4);
                  PyTuple_SetItem(args, 0, cb_self);
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyRegister(reg));
                  PyTuple_SetItem(args, 3, triton::bindings::python::PyLong_FromUint512(value));
                  Py_INCREF(cb_self);
                }
                else {
                  args = triton::bindings::python::xPyTuple_New(3);
                  PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyRegister(reg));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyLong_FromUint512(value));
                }

                /* Call the callback */
                Py_INCREF(cb);
                PyObject* ret = PyObject_CallObject(cb, args);

                /* Check the call */
                if (ret == nullptr) {
                  throw triton::exceptions::PyCallbacks();
                }

                Py_DECREF(args);
                /********* End of lambda *********/
              }, cb));
              break;

            case callbacks::SYMBOLIC_SIMPLIFICATION:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::symbolicSimplificationCallback([cb_self, cb](triton::API& api, triton::ast::SharedAbstractNode node) {
                /********* Lambda *********/
                PyObject* args = nullptr;

                /* Create function args */
                if (cb_self) {
                  args = triton::bindings::python::xPyTuple_New(3);
                  PyTuple_SetItem(args, 0, cb_self);
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 2, triton::bindings::python::PyAstNode(node));
                  Py_INCREF(cb_self);
                }
                else {
                  args = triton::bindings::python::xPyTuple_New(2);
                  PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyAstNode(node));
                }

                /* Call the callback */
                Py_INCREF(cb);
                PyObject* ret = PyObject_CallObject(cb, args);

                /* Check the call */
                if (ret == nullptr) {
                  throw triton::exceptions::PyCallbacks();
                }

                /* Check if the callback has returned a AbstractNode */
                if (!PyAstNode_Check(ret))
                  throw triton::exceptions::Callbacks("Callbacks::processCallbacks(SYMBOLIC_SIMPLIFICATION): You must return a AstNode object.");

                /* Update node */
                node = PyAstNode_AsAstNode(ret);
                Py_DECREF(args);
                return node;
                /********* End of lambda *********/
              }, cb));
              break;

            default:
              return PyErr_Format(PyExc_TypeError, "Callbacks::addCallback(): Invalid kind of callback.");
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_assignSymbolicExpressionToMemory(PyObject* self, PyObject* args) {
        PyObject* se  = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &se, &mem) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::assignSymbolicExpressionToMemory(): Invalid number of arguments");
        }

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::assignSymbolicExpressionToMemory(): Expects a SymbolicExpression as first argument.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::assignSymbolicExpressionToMemory(): Expects a MemoryAccess as second argument.");

        const triton::engines::symbolic::SharedSymbolicExpression& arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::MemoryAccess arg2 = *PyMemoryAccess_AsMemoryAccess(mem);

        try {
          PyTritonContext_AsTritonContext(self)->assignSymbolicExpressionToMemory(arg1, arg2);
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_assignSymbolicExpressionToRegister(PyObject* self, PyObject* args) {
        PyObject* se  = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &se, &reg) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::assignSymbolicExpressionToRegister(): Invalid number of arguments");
        }

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::assignSymbolicExpressionToRegister(): Expects a SymbolicExpression as first argument.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::assignSymbolicExpressionToRegister(): Expects a Register as second argument.");

        const triton::engines::symbolic::SharedSymbolicExpression& arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::Register arg2 = *PyRegister_AsRegister(reg);

        try {
          PyTritonContext_AsTritonContext(self)->assignSymbolicExpressionToRegister(arg1, arg2);
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_buildSemantics(PyObject* self, PyObject* inst) {
        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "TritonContext::buildSemantics(): Expects an Instruction as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->buildSemantics(*PyInstruction_AsInstruction(inst)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_clearCallbacks(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->clearCallbacks();
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_clearModes(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->clearModes();
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_clearConcreteMemoryValue(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &baseAddr, &size) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::clearConcreteMemoryValue(): Invalid number of arguments");
        }

        try {
          if (baseAddr && PyMemoryAccess_Check(baseAddr)) {
            PyTritonContext_AsTritonContext(self)->clearConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(baseAddr));
          }
          else if (baseAddr && (PyLong_Check(baseAddr) || PyInt_Check(baseAddr))) {
            if (size && (PyLong_Check(size) || PyInt_Check(size))) {
              PyTritonContext_AsTritonContext(self)->clearConcreteMemoryValue(PyLong_AsUint64(baseAddr), PyLong_AsUsize(size));
            }
            else {
              return PyErr_Format(PyExc_TypeError, "TritonContext::clearConcreteMemoryValue(): Expects a size (integer) as second argument.");
            }
          }
          else {
            return PyErr_Format(PyExc_TypeError, "TritonContext::clearConcreteMemoryValue(): Expects a base address (integer) as arguments or a memory cells.");
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_clearPathConstraints(PyObject* self, PyObject* args) {
        PyObject* tid = nullptr;

        if (PyArg_ParseTuple(args, "|O", &tid) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::clearPathConstraints(): Invalid number of arguments");
        }

        if (tid != nullptr && (!PyLong_Check(tid) && !PyInt_Check(tid))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::clearPathConstraints(): Expects an integer as thread id.");
        }

        try {
          if (tid == nullptr) {
            PyTritonContext_AsTritonContext(self)->clearPathConstraints();
          }
          else {
            PyTritonContext_AsTritonContext(self)->clearPathConstraints(PyLong_AsUint32(tid));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeAllMemory(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->concretizeAllMemory();
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeAllRegister(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->concretizeAllRegister();
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeMemory(PyObject* self, PyObject* mem) {
        /* If mem is an address */
        if (PyLong_Check(mem) || PyInt_Check(mem)) {
          try {
            PyTritonContext_AsTritonContext(self)->concretizeMemory(PyLong_AsUint64(mem));
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* If mem is a MemoryAccess */
        else if (PyMemoryAccess_Check(mem)) {
          try {
            PyTritonContext_AsTritonContext(self)->concretizeMemory(*PyMemoryAccess_AsMemoryAccess(mem));
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* Invalid parameter */
        else
          return PyErr_Format(PyExc_TypeError, "TritonContext::concretizeMemory(): Expects an integer or MemoryAccess as argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::concretizeRegister(): Expects a Register as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->concretizeRegister(*PyRegister_AsRegister(reg));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_createSymbolicMemoryExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* mem           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OOOO", &inst, &node, &mem, &comment) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicMemoryExpression(): Invalid number of arguments");
        }

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicMemoryExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicMemoryExpression(): Expects a AstNode as second argument.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicMemoryExpression(): Expects a MemoryAccess as third argument.");

        if (comment != nullptr && !PyStr_Check(comment))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicMemoryExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyStr_AsString(comment);

        triton::arch::Instruction& arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);
        triton::arch::MemoryAccess arg3 = *PyMemoryAccess_AsMemoryAccess(mem);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicMemoryExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_createSymbolicRegisterExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* reg           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OOOO", &inst, &node, &reg, &comment) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicRegisterExpression(): Invalid number of arguments");
        }

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicRegisterExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicRegisterExpression(): Expects a AstNode as second argument.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicRegisterExpression(): Expects a Register as third argument.");

        if (comment != nullptr && !PyStr_Check(comment))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicRegisterExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyStr_AsString(comment);

        triton::arch::Instruction& arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);
        triton::arch::Register arg3 = *PyRegister_AsRegister(reg);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicRegisterExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_createSymbolicVolatileExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OOO", &inst, &node, &comment) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicVolatileExpression(): Invalid number of arguments");
        }

        if (inst == nullptr || (!PyInstruction_Check(inst)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicVolatileExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicVolatileExpression(): Expects a AstNode as second argument.");

        if (comment != nullptr && !PyStr_Check(comment))
          return PyErr_Format(PyExc_TypeError, "TritonContext::createSymbolicVolatileExpression(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyStr_AsString(comment);

        triton::arch::Instruction& arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicVolatileExpression(arg1, arg2, ccomment));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_disassembly(PyObject* self, PyObject* inst) {
        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "TritonContext::disassembly(): Expects an Instruction as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->disassembly(*PyInstruction_AsInstruction(inst));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_enableSymbolicEngine(PyObject* self, PyObject* flag) {
        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::enableSymbolicEngine(): Expects an boolean as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->enableSymbolicEngine(PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_enableTaintEngine(PyObject* self, PyObject* flag) {
        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::enableTaintEngine(): Expects an boolean as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->enableTaintEngine(PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_evaluateAstViaZ3(PyObject* self, PyObject* node) {
        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "TritonContext::evaluateAstViaZ3(): Expects a AstNode as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->evaluateAstViaZ3(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_getAllRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          triton::uint32 index = 0;
          auto& regs = PyTritonContext_AsTritonContext(self)->getAllRegisters();

          ret = xPyList_New(regs.size());
          for (auto& reg: regs)
            PyList_SetItem(ret, index++, PyRegister(reg.second));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getArchitecture(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getArchitecture());
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getAstContext(PyObject* self, PyObject* noarg) {
        try {
          return PyAstContext(PyTritonContext_AsTritonContext(self)->getAstContext());
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getAstRepresentationMode(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getAstRepresentationMode());
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getConcreteMemoryAreaValue(PyObject* self, PyObject* args) {
        triton::uint8*  area = nullptr;
        PyObject*       ret  = nullptr;
        PyObject*       addr = nullptr;
        PyObject*       size = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &addr, &size) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getConcreteMemoryAreaValue(): Invalid number of arguments");
        }

        try {
          std::vector<triton::uint8> vv = PyTritonContext_AsTritonContext(self)->getConcreteMemoryAreaValue(PyLong_AsUint64(addr), PyLong_AsUsize(size));
          area = new triton::uint8[vv.size()];

          for (triton::usize index = 0; index < vv.size(); index++)
            area[index] = vv[index];

          ret = PyBytes_FromStringAndSize(reinterpret_cast<const char*>(area), vv.size());
          delete[] area;
          return ret;

        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getConcreteMemoryValue(PyObject* self, PyObject* mem) {
        try {
          if (PyLong_Check(mem) || PyInt_Check(mem))
              return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteMemoryValue(PyLong_AsUint64(mem)));
          else if (PyMemoryAccess_Check(mem))
              return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::getConcreteMemoryValue(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getConcreteRegisterValue(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getConcreteRegisterValue(): Expects a Register as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getConcreteVariableValue(PyObject* self, PyObject* symVar) {
        if (!PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getConcreteVariableValue(): Expects a SymbolicVariable as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteVariableValue(PySymbolicVariable_AsSymbolicVariable(symVar)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getGprBitSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getGprBitSize());
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getGprSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getGprSize());
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getImmediateAst(PyObject* self, PyObject* imm) {
        if (!PyImmediate_Check(imm))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getImmediateAst(): Expects an Immediate as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getImmediateAst(*PyImmediate_AsImmediate(imm)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getMemoryAst(PyObject* self, PyObject* mem) {
        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getMemoryAst(): Expects an MemoryAccess as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getMemoryAst(*PyMemoryAccess_AsMemoryAccess(mem)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getModel(PyObject* self, PyObject* node) {
        PyObject* ret = nullptr;

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getModel(): Expects a AstNode as argument.");

        try {
          ret = xPyDict_New();
          auto model = PyTritonContext_AsTritonContext(self)->getModel(PyAstNode_AsAstNode(node));
          for (auto it = model.begin(); it != model.end(); it++) {
            xPyDict_SetItem(ret, PyLong_FromUsize(it->first), PySolverModel(it->second));
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getModels(PyObject* self, PyObject* args) {
        PyObject* ret   = nullptr;
        PyObject* node  = nullptr;
        PyObject* limit = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &node, &limit) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getModels(): Invalid number of arguments");
        }

        if (node == nullptr || !PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getModels(): Expects a AstNode as first argument.");

        if (limit == nullptr || (!PyLong_Check(limit) && !PyInt_Check(limit)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getModels(): Expects an integer as second argument.");

        try {
          auto models = PyTritonContext_AsTritonContext(self)->getModels(PyAstNode_AsAstNode(node), PyLong_AsUint32(limit));
          triton::uint32 index = 0;

          ret = xPyList_New(models.size());
          for (auto it = models.begin(); it != models.end(); it++) {
            PyObject* mdict = xPyDict_New();
            auto model = *it;

            for (auto it2 = model.begin(); it2 != model.end(); it2++) {
              xPyDict_SetItem(mdict, PyLong_FromUsize(it2->first), PySolverModel(it2->second));
            }
            if (model.size() > 0)
              PyList_SetItem(ret, index++, mdict);
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getParentRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          triton::uint32 index = 0;
          auto regs = PyTritonContext_AsTritonContext(self)->getParentRegisters();

          ret = xPyList_New(regs.size());
          for (const auto* reg: regs) {
            PyList_SetItem(ret, index++, PyRegister(*reg));
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getPathConstraints(PyObject* self, PyObject* args) {
        PyObject* pytid    = nullptr;
        PyObject* ret      = nullptr;
        triton::uint32 tid = 0;

        if (PyArg_ParseTuple(args, "|O", &pytid) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPathConstraints(): Invalid number of arguments");
        }

        if (pytid != nullptr && (!PyLong_Check(pytid) && !PyInt_Check(pytid))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPathConstraints(): Expects an integer as thread id.");
        }

        if (pytid != nullptr) {
          tid = PyLong_AsUint32(pytid);
        }

        try {
          triton::uint32 index = 0;
          auto pc = PyTritonContext_AsTritonContext(self)->getPathConstraints(tid);

          ret = xPyList_New(pc.size());
          for (auto it = pc.begin(); it != pc.end(); it++) {
            PyList_SetItem(ret, index++, PyPathConstraint(*it));
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getPathPredicate(PyObject* self, PyObject* args) {
        PyObject* pytid = nullptr;

        if (PyArg_ParseTuple(args, "|O", &pytid) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPathPredicate(): Invalid number of arguments");
        }

        if (pytid != nullptr && (!PyLong_Check(pytid) && !PyInt_Check(pytid))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPathPredicate(): Expects an integer as thread id.");
        }

        try {
          if (pytid == nullptr) {
            return PyAstNode(PyTritonContext_AsTritonContext(self)->getPathPredicate());
          }
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getPathPredicate(PyLong_AsUint32(pytid)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getPredicatesToReachAddress(PyObject* self, PyObject* args) {
        PyObject* ret    = nullptr;
        PyObject* pytid  = nullptr;
        PyObject* pyaddr = nullptr;

        if (PyArg_ParseTuple(args, "|OO", &pyaddr, &pytid) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPredicatesToReachAddress(): Invalid number of arguments");
        }

        if (pyaddr == nullptr || (!PyLong_Check(pyaddr) && !PyInt_Check(pyaddr))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPredicatesToReachAddress(): Expects an address as argument.");
        }

        if (pytid != nullptr && (!PyLong_Check(pytid) && !PyInt_Check(pytid))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getPredicatesToReachAddress(): Expects an integer as thread id.");
        }

        try {
          triton::uint32 index = 0;
          triton::uint32 tid   = 0;
          triton::uint64 addr  = PyLong_AsUint64(pyaddr);

          if (pytid != nullptr) {
            tid = PyLong_AsUint32(pytid);
          }

          auto preds = PyTritonContext_AsTritonContext(self)->getPredicatesToReachAddress(addr, tid);

          ret = xPyList_New(preds.size());
          for (auto it = preds.begin(); it != preds.end(); it++) {
            PyList_SetItem(ret, index++, PyAstNode(*it));
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getRegister(PyObject* self, PyObject* regIn) {
        triton::arch::register_e rid = triton::arch::ID_REG_INVALID;

        if (regIn == nullptr || (!PyLong_Check(regIn) && !PyInt_Check(regIn)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getRegister(): Expects an id as argument.");

        try {
          rid = static_cast<triton::arch::register_e>(PyLong_AsUint32(regIn));
          triton::arch::Register regOut(PyTritonContext_AsTritonContext(self)->getRegister(rid));
          return PyRegister(regOut);
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getRegisterAst(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getRegisterAst(): Expects an Register as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getRegisterAst(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicExpression(PyObject* self, PyObject* symExprId) {
        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicExpression(): Expects an integer as argument.");

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->getSymbolicExpression(PyLong_AsUsize(symExprId)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicExpressions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const auto& expressions = PyTritonContext_AsTritonContext(self)->getSymbolicExpressions();

          ret = xPyDict_New();
          for (auto it = expressions.begin(); it != expressions.end(); it++)
            xPyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicMemory(PyObject* self, PyObject* args) {
        PyObject* ret  = nullptr;
        PyObject* addr = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|O", &addr) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicMemory(): Invalid number of arguments");
        }

        try {
          if (addr == nullptr) {
            auto regs = PyTritonContext_AsTritonContext(self)->getSymbolicMemory();

            ret = xPyDict_New();
            for (auto it = regs.begin(); it != regs.end(); it++) {
              xPyDict_SetItem(ret, PyLong_FromUint64(it->first), PySymbolicExpression(it->second));
            }
          }
          else if (addr != nullptr && (PyLong_Check(addr) || PyInt_Check(addr))) {
            ret = PySymbolicExpression(PyTritonContext_AsTritonContext(self)->getSymbolicMemory(PyLong_AsUint64(addr)));
          }
          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicMemory(): Expects an integer or nothing as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicMemoryValue(PyObject* self, PyObject* mem) {
        if (!PyLong_Check(mem) && !PyInt_Check(mem) && !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicMemoryValue(): Expects an integer or a MemoryAccess as argument.");

        try {
          if (PyLong_Check(mem) || PyInt_Check(mem))
            return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getSymbolicMemoryValue(PyLong_AsUint64(mem)));
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getSymbolicMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          auto regs = PyTritonContext_AsTritonContext(self)->getSymbolicRegisters();

          ret = xPyDict_New();
          for (auto it = regs.begin(); it != regs.end(); it++) {
            xPyDict_SetItem(ret, PyLong_FromUint64(it->first), PySymbolicExpression(it->second));
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicRegister(): Expects a Register as argument.");

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->getSymbolicRegister(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicRegisterValue(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicRegisterValue(): Expects a Register as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getSymbolicRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicVariable(PyObject* self, PyObject* arg) {
        try {
          if (PyLong_Check(arg) || PyInt_Check(arg))
            return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->getSymbolicVariable(PyLong_AsUsize(arg)));

          else if (PyStr_Check(arg))
            return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->getSymbolicVariable(PyStr_AsString(arg)));

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::getSymbolicVariable(): Expects an integer or a string as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicVariables(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          const auto& variables = PyTritonContext_AsTritonContext(self)->getSymbolicVariables();

          ret = xPyDict_New();
          for (auto sv: variables)
            xPyDict_SetItem(ret, PyLong_FromUsize(sv.first), PySymbolicVariable(sv.second));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getTaintedMemory(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        try {
          std::unordered_set<triton::uint64> addresses = PyTritonContext_AsTritonContext(self)->getTaintedMemory();

          size = addresses.size();
          ret = xPyList_New(size);
          for (auto it = addresses.begin(); it != addresses.end(); it++) {
            PyList_SetItem(ret, index, PyLong_FromUint64(*it));
            index++;
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getTaintedRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        try {
          std::unordered_set<const triton::arch::Register*> registers = PyTritonContext_AsTritonContext(self)->getTaintedRegisters();

          size = registers.size();
          ret = xPyList_New(size);
          for (const auto* reg: registers) {
            PyList_SetItem(ret, index, PyRegister(*reg));
            index++;
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getTaintedSymbolicExpressions(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        try {
          auto expressions = PyTritonContext_AsTritonContext(self)->getTaintedSymbolicExpressions();

          size = expressions.size();
          ret = xPyList_New(size);
          for (auto it = expressions.begin(); it != expressions.end(); it++) {
            PyList_SetItem(ret, index, PySymbolicExpression(*it));
            index++;
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_isArchitectureValid(PyObject* self, PyObject* noarg) {
        try {
          if (PyTritonContext_AsTritonContext(self)->isArchitectureValid() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isConcreteMemoryValueDefined(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &baseAddr, &size) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::isConcreteMemoryValueDefined(): Invalid number of arguments");
        }

        try {
          if (baseAddr && PyMemoryAccess_Check(baseAddr)) {
            if (PyTritonContext_AsTritonContext(self)->isConcreteMemoryValueDefined(*PyMemoryAccess_AsMemoryAccess(baseAddr)) == true)
              Py_RETURN_TRUE;
            Py_RETURN_FALSE;
          }
          else if (baseAddr && (PyLong_Check(baseAddr) || PyInt_Check(baseAddr))) {
            if (size && (PyLong_Check(size) || PyInt_Check(size))) {
              if (PyTritonContext_AsTritonContext(self)->isConcreteMemoryValueDefined(PyLong_AsUint64(baseAddr), PyLong_AsUsize(size)) == true)
                Py_RETURN_TRUE;
              Py_RETURN_FALSE;
            }
            else {
              return PyErr_Format(PyExc_TypeError, "TritonContext::isConcreteMemoryValueDefined(): Expects a size (integer) as second argument.");
            }
          }
          else {
            return PyErr_Format(PyExc_TypeError, "TritonContext::isConcreteMemoryValueDefined(): Expects a base address (integer) as arguments or a memory cells.");
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isFlag(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isFlag(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isFlag(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isMemorySymbolized(PyObject* self, PyObject* mem) {
        try {
          if (PyMemoryAccess_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->isMemorySymbolized(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
              Py_RETURN_TRUE;
          }

          else if (PyLong_Check(mem) || PyInt_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->isMemorySymbolized(PyLong_AsUint64(mem)) == true)
              Py_RETURN_TRUE;
          }

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::isMemorySymbolized(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isMemoryTainted(PyObject* self, PyObject* mem) {
        try {
          if (PyMemoryAccess_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->isMemoryTainted(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
              Py_RETURN_TRUE;
          }

          else if (PyLong_Check(mem) || PyInt_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->isMemoryTainted(PyLong_AsUint64(mem)) == true)
              Py_RETURN_TRUE;
          }

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::isMemoryTainted(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isRegister(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isRegisterSymbolized(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isRegisterSymbolized(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegisterSymbolized(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isRegisterTainted(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isRegisterTainted(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegisterTainted(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isRegisterValid(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isRegisterValid(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegisterValid(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isSat(PyObject* self, PyObject* node) {
        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isSat(): Expects a AstNode as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isSat(PyAstNode_AsAstNode(node)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isSymbolicEngineEnabled(PyObject* self, PyObject* noarg) {
        try {
          if (PyTritonContext_AsTritonContext(self)->isSymbolicEngineEnabled() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isSymbolicExpressionExists(PyObject* self, PyObject* symExprId) {
        if (!PyInt_Check(symExprId) && !PyLong_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isSymbolicExpressionExists(): Expects an integer as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isSymbolicExpressionExists(PyLong_AsUsize(symExprId)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isModeEnabled(PyObject* self, PyObject* mode) {
        if (!PyInt_Check(mode) && !PyLong_Check(mode))
          return PyErr_Format(PyExc_TypeError, "TritonContext::isModeEnabled(): Expects a MODE as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isModeEnabled(static_cast<triton::modes::mode_e>(PyLong_AsUint32(mode))) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isTaintEngineEnabled(PyObject* self, PyObject* noarg) {
        try {
          if (PyTritonContext_AsTritonContext(self)->isTaintEngineEnabled() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }

      static PyObject* TritonContext_isThumb(PyObject* self, PyObject* noarg) {
        try {
          if (PyTritonContext_AsTritonContext(self)->isThumb() == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }

      static PyObject* TritonContext_newSymbolicExpression(PyObject* self, PyObject* args) {
        PyObject* node          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &node, &comment) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::newSymbolicExpression(): Invalid number of arguments");
        }

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::newSymbolicExpression(): Expects a AstNode as first argument.");

        if (comment != nullptr && !PyStr_Check(comment))
          return PyErr_Format(PyExc_TypeError, "TritonContext::newSymbolicExpression(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyStr_AsString(comment);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->newSymbolicExpression(PyAstNode_AsAstNode(node), ccomment));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_newSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* size      = nullptr;
        PyObject* alias     = nullptr;
        std::string calias  = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &size, &alias) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::newSymbolicVariable(): Invalid number of arguments");
        }

        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::newSymbolicVariable(): Expects an integer as first argument.");

        if (alias != nullptr && !PyStr_Check(alias))
          return PyErr_Format(PyExc_TypeError, "TritonContext::newSymbolicVariable(): Expects a sting as second  argument.");

        if (alias != nullptr)
          calias = PyStr_AsString(alias);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->newSymbolicVariable(PyLong_AsUint32(size), calias));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_popPathConstraint(PyObject* self, PyObject* args) {
        PyObject* tid = nullptr;

        if (PyArg_ParseTuple(args, "|O", &tid) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::popPathConstraint(): Invalid number of arguments");
        }

        if (tid != nullptr && (!PyLong_Check(tid) && !PyInt_Check(tid))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::popPathConstraint(): Expects an integer as thread id.");
        }

        try {
          if (tid == nullptr) {
            PyTritonContext_AsTritonContext(self)->popPathConstraint();
          }
          else {
            PyTritonContext_AsTritonContext(self)->popPathConstraint(PyLong_AsUint32(tid));
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_printSlicedExpressions(PyObject* self, PyObject* args) {
        PyObject* expr        = nullptr;
        PyObject* assertFlag  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &expr, &assertFlag) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::printSlicedExpressions(): Invalid number of arguments");
        }

        if (expr == nullptr || !PySymbolicExpression_Check(expr))
          return PyErr_Format(PyExc_TypeError, "TritonContext::printSlicedExpressions(): Expects a SymbolicExpression as first argument.");

        if (assertFlag != nullptr && !PyBool_Check(assertFlag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::printSlicedExpressions(): Expects a boolean as second argument.");

        if (assertFlag == nullptr)
          assertFlag = PyLong_FromUint32(false);

        try {
          PyTritonContext_AsTritonContext(self)->printSlicedExpressions(std::cout, PySymbolicExpression_AsSymbolicExpression(expr), PyLong_AsBool(assertFlag));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_processing(PyObject* self, PyObject* inst) {
        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "TritonContext::processing(): Expects an Instruction as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->processing(*PyInstruction_AsInstruction(inst)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_pushPathConstraint(PyObject* self, PyObject* args) {
        PyObject* node = nullptr;
        PyObject* tid  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &node, &tid) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::pushPathConstraint(): Invalid number of arguments");
        }

        if (!PyAstNode_Check(node)) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::pushPathConstraint(): Expects an AstNode as argument.");
        }

        if (tid != nullptr && (!PyLong_Check(tid) && !PyInt_Check(tid))) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::pushPathConstraint(): Expects an integer as thread id.");
        }

        try {
          if (tid == nullptr) {
            PyTritonContext_AsTritonContext(self)->pushPathConstraint(PyAstNode_AsAstNode(node));
          }
          else {
            PyTritonContext_AsTritonContext(self)->pushPathConstraint(PyAstNode_AsAstNode(node), PyLong_AsUint32(tid));
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_removeCallback(PyObject* self, PyObject* args) {
        PyObject* cb       = nullptr;
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &function, &mode) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::removeCallback(): Invalid number of arguments");
        }

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "TritonContext::removeCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::removeCallback(): Expects a CALLBACK as second argument.");

        /* Get the callback (class or static) */
        cb = (PyMethod_Check(function) ? PyMethod_GET_FUNCTION(function) : function);

        try {
          switch (static_cast<triton::callbacks::callback_e>(PyLong_AsUint32(mode))) {
            case callbacks::GET_CONCRETE_MEMORY_VALUE:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::getConcreteMemoryValueCallback(nullptr, cb));
              break;
            case callbacks::GET_CONCRETE_REGISTER_VALUE:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::getConcreteRegisterValueCallback(nullptr, cb));
              break;
            case callbacks::SET_CONCRETE_MEMORY_VALUE:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::setConcreteMemoryValueCallback(nullptr, cb));
              break;
            case callbacks::SET_CONCRETE_REGISTER_VALUE:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::setConcreteRegisterValueCallback(nullptr, cb));
              break;
            case callbacks::SYMBOLIC_SIMPLIFICATION:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::symbolicSimplificationCallback(nullptr, cb));
              break;
            default:
              return PyErr_Format(PyExc_TypeError, "TritonContext::removeCallback(): Invalid kind of callback.");
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_reset(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->reset();
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setArchitecture(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setArchitecture(): Expects an ARCH as argument.");

        try {
          /* Set the architecture */
          PyTritonContext_AsTritonContext(self)->setArchitecture(static_cast<triton::arch::architecture_e>(PyLong_AsUint32(arg)));
          TritonContext_fillRegistersAttribute(self);
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setAstRepresentationMode(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setAstRepresentationMode(): Expects an AST_REPRESENTATION as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->setAstRepresentationMode(PyLong_AsUint32(arg));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setConcreteMemoryAreaValue(PyObject* self, PyObject* args) {
        std::vector<triton::uint8> vv;
        PyObject* baseAddr  = nullptr;
        PyObject* values    = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &baseAddr, &values) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryAreaValue(): Invalid number of arguments");
        }

        if (baseAddr == nullptr || (!PyLong_Check(baseAddr) && !PyInt_Check(baseAddr)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryAreaValue(): Expects an integer as first argument.");

        if (values == nullptr)
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryAreaValue(): Expects a list or bytes as second argument.");

        // Python object: List
        if (PyList_Check(values)) {
          for (Py_ssize_t i = 0; i < PyList_Size(values); i++) {
            PyObject* item = PyList_GetItem(values, i);

            if ((!PyLong_Check(item) && !PyInt_Check(item)) || PyLong_AsUint32(item) > 0xff)
              return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryAreaValue(): Each item of the list must be a 8-bits integer.");

            vv.push_back(static_cast<triton::uint8>(PyLong_AsUint32(item) & 0xff));
          }

          try {
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), vv);
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
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
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), area, size);
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
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
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), area, size);
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        // Invalid Python object
        else
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryAreaValue(): Expects a list or bytes as second argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setConcreteMemoryValue(PyObject* self, PyObject* args) {
        PyObject* mem    = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &mem, &value) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryValue(): Invalid number of arguments");
        }

        /* setConcreteMemoryValue(integer, integer) */
        if (mem != nullptr && (PyLong_Check(mem) || PyInt_Check(mem))) {
          if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
            return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryValue(): Expects a value as second argument.");

          triton::uint64 addr   = PyLong_AsUint64(mem);
          triton::uint32 cvalue = PyLong_AsUint32(value);

          if (cvalue > 0xff)
            return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryValue(): Value must be on 8 bits.");

          try {
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryValue(addr, static_cast<triton::uint8>(cvalue & 0xff));
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }

        }

        /* setConcreteMemoryValue(MemoryAccess) */
        else if (mem != nullptr && PyMemoryAccess_Check(mem)) {
          if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
            return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryValue(): Expects a value as second argument.");
          try {
            triton::uint512 cvalue = PyLong_AsUint512(value);
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem), cvalue);
          }
          catch (const triton::exceptions::PyCallbacks&) {
            return nullptr;
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* Invalid */
        else
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteMemoryValue(): Expects a MemoryAccess or an integer as first argument.");

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setConcreteRegisterValue(PyObject* self, PyObject* args) {
        PyObject* reg    = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &reg, &value) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteRegisterValue(): Invalid number of arguments");
        }

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteRegisterValue(): Expects a Register as first argument.");

        if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteRegisterValue(): Expects a value as second argument.");

        try {
          triton::uint512 cvalue = PyLong_AsUint512(value);
          PyTritonContext_AsTritonContext(self)->setConcreteRegisterValue(*PyRegister_AsRegister(reg), cvalue);
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setConcreteVariableValue(PyObject* self, PyObject* args) {
        PyObject* symVar = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &symVar, &value) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteVariableValue(): Invalid number of arguments");
        }

        if (symVar == nullptr || !PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteVariableValue(): Bad argument type.");

        if (value == nullptr)
          return PyErr_Format(PyExc_TypeError, "TritonContext::setConcreteVariableValue(): Expects a second argument as integer value.");

        try {
          PyTritonContext_AsTritonContext(self)->setConcreteVariableValue(PySymbolicVariable_AsSymbolicVariable(symVar), PyLong_AsUint512(value));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setMode(PyObject* self, PyObject* args) {
        PyObject* mode = nullptr;
        PyObject* flag = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &mode, &flag) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setMode(): Invalid number of arguments");
        }

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setMode(): Expects a MODE as argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setMode(): Expects an boolean flag as second argument.");

        try {
          PyTritonContext_AsTritonContext(self)->setMode(static_cast<triton::modes::mode_e>(PyLong_AsUint32(mode)), PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setTaintMemory(PyObject* self, PyObject* args) {
        PyObject* mem  = nullptr;
        PyObject* flag = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &mem, &flag) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setTaintMemory(): Invalid number of arguments");
        }

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setTaintMemory(): Expects a MemoryAccess as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setTaintMemory(): Expects a boolean as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->setTaintMemory(*PyMemoryAccess_AsMemoryAccess(mem), PyLong_AsBool(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_setTaintRegister(PyObject* self, PyObject* args) {
        PyObject* reg    = nullptr;
        PyObject* flag   = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &reg, &flag) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::setTaintRegister(): Invalid number of arguments");
        }

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setTaintRegister(): Expects a Register as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setTaintRegister(): Expects a boolean as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->setTaintRegister(*PyRegister_AsRegister(reg), PyLong_AsBool(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_setThumb(PyObject* self, PyObject* state) {
        if (state == nullptr || !PyBool_Check(state))
          return PyErr_Format(PyExc_TypeError, "TritonContext::setThumb(): Expects an boolean as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->setThumb(PyLong_AsBool(state));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_simplify(PyObject* self, PyObject* args) {
        PyObject* node        = nullptr;
        PyObject* z3Flag      = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &node, &z3Flag) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::simplify(): Invalid number of arguments");
        }

        if (node == nullptr || !PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "TritonContext::simplify(): Expects a AstNode as first argument.");

        if (z3Flag != nullptr && !PyBool_Check(z3Flag))
          return PyErr_Format(PyExc_TypeError, "TritonContext::simplify(): Expects a boolean as second argument.");

        if (z3Flag == nullptr)
          z3Flag = PyLong_FromUint32(false);

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->processSimplification(PyAstNode_AsAstNode(node), PyLong_AsBool(z3Flag)));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_sliceExpressions(PyObject* self, PyObject* expr) {
        PyObject* ret = nullptr;

        if (!PySymbolicExpression_Check(expr))
          return PyErr_Format(PyExc_TypeError, "TritonContext::sliceExpressions(): Expects a SymbolicExpression as argument.");

        try {
          auto exprs = PyTritonContext_AsTritonContext(self)->sliceExpressions(PySymbolicExpression_AsSymbolicExpression(expr));

          ret = xPyDict_New();
          for (auto it = exprs.begin(); it != exprs.end(); it++)
            xPyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_symbolizeExpression(PyObject* self, PyObject* args) {
        PyObject* exprId        = nullptr;
        PyObject* symVarSize    = nullptr;
        PyObject* symVarAlias   = nullptr;
        std::string calias      = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OOO", &exprId, &symVarSize, &symVarAlias) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeExpression(): Invalid number of arguments");
        }

        if (exprId == nullptr || (!PyLong_Check(exprId) && !PyInt_Check(exprId)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeExpression(): Expects an integer as first argument.");

        if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeExpression(): Expects an integer as second argument.");

        if (symVarAlias != nullptr && !PyStr_Check(symVarAlias))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeExpression(): Expects a sting as third argument.");

        if (symVarAlias != nullptr)
          calias = PyStr_AsString(symVarAlias);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->symbolizeExpression(PyLong_AsUsize(exprId), PyLong_AsUint32(symVarSize), calias));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_symbolizeMemory(PyObject* self, PyObject* args) {
        PyObject* mem           = nullptr;
        PyObject* symVarAlias   = nullptr;
        std::string calias      = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &mem, &symVarAlias) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeMemory(): Invalid number of arguments");
        }

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeMemory(): Expects a MemoryAccess as first argument.");

        if (symVarAlias != nullptr && !PyStr_Check(symVarAlias))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeMemory(): Expects a sting as second argument.");

        if (symVarAlias != nullptr)
          calias = PyStr_AsString(symVarAlias);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->symbolizeMemory(*PyMemoryAccess_AsMemoryAccess(mem), calias));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_symbolizeRegister(PyObject* self, PyObject* args) {
        PyObject* reg           = nullptr;
        PyObject* symVarAlias   = nullptr;
        std::string calias      = "";

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &reg, &symVarAlias) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeRegister(): Invalid number of arguments");
        }

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeRegister(): Expects a Register as first argument.");

        if (symVarAlias != nullptr && !PyStr_Check(symVarAlias))
          return PyErr_Format(PyExc_TypeError, "TritonContext::symbolizeRegister(): Expects a sting as second argument.");

        if (symVarAlias != nullptr)
          calias = PyStr_AsString(symVarAlias);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->symbolizeRegister(*PyRegister_AsRegister(reg), calias));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintAssignment(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        bool ret      = false;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "OO", &op1, &op2) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::taintAssignment(): Invalid number of arguments");
        }

        try {
          if (PyMemoryAccess_Check(op1) && PyImmediate_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintAssignment(*PyMemoryAccess_AsMemoryAccess(op1), *PyImmediate_AsImmediate(op2));

          else if (PyMemoryAccess_Check(op1) && PyMemoryAccess_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintAssignment(*PyMemoryAccess_AsMemoryAccess(op1), *PyMemoryAccess_AsMemoryAccess(op2));

          else if (PyMemoryAccess_Check(op1) && PyRegister_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintAssignment(*PyMemoryAccess_AsMemoryAccess(op1), *PyRegister_AsRegister(op2));

          else if (PyRegister_Check(op1) && PyImmediate_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintAssignment(*PyRegister_AsRegister(op1), *PyImmediate_AsImmediate(op2));

          else if (PyRegister_Check(op1) && PyMemoryAccess_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintAssignment(*PyRegister_AsRegister(op1), *PyMemoryAccess_AsMemoryAccess(op2));

          else if (PyRegister_Check(op1) && PyRegister_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintAssignment(*PyRegister_AsRegister(op1), *PyRegister_AsRegister(op2));

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::taintAssignment(): Invalid kind of parameter.");

          if (ret == true) {
            Py_RETURN_TRUE;
          }
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintMemory(PyObject* self, PyObject* mem) {
        try {
          if (PyMemoryAccess_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->taintMemory(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
              Py_RETURN_TRUE;
          }

          else if (PyLong_Check(mem) || PyInt_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->taintMemory(PyLong_AsUint64(mem)) == true)
              Py_RETURN_TRUE;
          }

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::taintMemory(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_taintRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::taintRegister(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnion(PyObject* self, PyObject* args) {
        PyObject* op1 = nullptr;
        PyObject* op2 = nullptr;
        bool ret      = false;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "OO", &op1, &op2) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext::taintUnion(): Invalid number of arguments");
        }

        try {
          if (PyMemoryAccess_Check(op1) && PyImmediate_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintUnion(*PyMemoryAccess_AsMemoryAccess(op1), *PyImmediate_AsImmediate(op2));

          else if (PyMemoryAccess_Check(op1) && PyMemoryAccess_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintUnion(*PyMemoryAccess_AsMemoryAccess(op1), *PyMemoryAccess_AsMemoryAccess(op2));

          else if (PyMemoryAccess_Check(op1) && PyRegister_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintUnion(*PyMemoryAccess_AsMemoryAccess(op1), *PyRegister_AsRegister(op2));

          else if (PyRegister_Check(op1) && PyImmediate_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintUnion(*PyRegister_AsRegister(op1), *PyImmediate_AsImmediate(op2));

          else if (PyRegister_Check(op1) && PyMemoryAccess_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintUnion(*PyRegister_AsRegister(op1), *PyMemoryAccess_AsMemoryAccess(op2));

          else if (PyRegister_Check(op1) && PyRegister_Check(op2))
            ret = PyTritonContext_AsTritonContext(self)->taintUnion(*PyRegister_AsRegister(op1), *PyRegister_AsRegister(op2));

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::taintUnion(): Invalid kind of parameter.");

          if (ret == true) {
            Py_RETURN_TRUE;
          }
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_untaintMemory(PyObject* self, PyObject* mem) {
        try {
          if (PyMemoryAccess_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->untaintMemory(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
              Py_RETURN_TRUE;
          }

          else if (PyLong_Check(mem) || PyInt_Check(mem)) {
            if (PyTritonContext_AsTritonContext(self)->untaintMemory(PyLong_AsUint64(mem)) == true)
              Py_RETURN_TRUE;
          }

          else
            return PyErr_Format(PyExc_TypeError, "TritonContext::untaintMemory(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_untaintRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::untaintRegister(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->untaintRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getParentRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "TritonContext::getParentRegister(): Expects a Register as argument.");

        try {
          return PyRegister(PyTritonContext_AsTritonContext(self)->getParentRegister(PyRegister_AsRegister(reg)->getId()));
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getattro(PyObject* self, PyObject* name) {
        try {
          /* Access to the registers attribute */
          if (std::string(PyStr_AsString(name)) == "registers") {

            /* Check if the architecture is defined */
            if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
              return PyErr_Format(PyExc_TypeError, "__getattr__.registers: Architecture is not defined.");

            /* Maybe null if TritonContext was created over the PyTritonContextRef function */
            if (((TritonContext_Object*)(self))->regAttr == nullptr)
              TritonContext_fillRegistersAttribute(self);

            Py_INCREF(((TritonContext_Object*)(self))->regAttr);
            return ((TritonContext_Object*)(self))->regAttr;
          }
        }
        catch (const triton::exceptions::PyCallbacks&) {
          return nullptr;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return PyObject_GenericGetAttr((PyObject *)self, name);
      }


      //! TritonContext methods.
      PyMethodDef TritonContext_callbacks[] = {
        {"addCallback",                         (PyCFunction)TritonContext_addCallback,                            METH_VARARGS,       ""},
        {"assignSymbolicExpressionToMemory",    (PyCFunction)TritonContext_assignSymbolicExpressionToMemory,       METH_VARARGS,       ""},
        {"assignSymbolicExpressionToRegister",  (PyCFunction)TritonContext_assignSymbolicExpressionToRegister,     METH_VARARGS,       ""},
        {"buildSemantics",                      (PyCFunction)TritonContext_buildSemantics,                         METH_O,             ""},
        {"clearCallbacks",                      (PyCFunction)TritonContext_clearCallbacks,                         METH_NOARGS,        ""},
        {"clearModes",                          (PyCFunction)TritonContext_clearModes,                             METH_NOARGS,        ""},
        {"clearConcreteMemoryValue",            (PyCFunction)TritonContext_clearConcreteMemoryValue,               METH_VARARGS,       ""},
        {"clearPathConstraints",                (PyCFunction)TritonContext_clearPathConstraints,                   METH_VARARGS,       ""},
        {"concretizeAllMemory",                 (PyCFunction)TritonContext_concretizeAllMemory,                    METH_NOARGS,        ""},
        {"concretizeAllRegister",               (PyCFunction)TritonContext_concretizeAllRegister,                  METH_NOARGS,        ""},
        {"concretizeMemory",                    (PyCFunction)TritonContext_concretizeMemory,                       METH_O,             ""},
        {"concretizeRegister",                  (PyCFunction)TritonContext_concretizeRegister,                     METH_O,             ""},
        {"createSymbolicMemoryExpression",      (PyCFunction)TritonContext_createSymbolicMemoryExpression,         METH_VARARGS,       ""},
        {"createSymbolicRegisterExpression",    (PyCFunction)TritonContext_createSymbolicRegisterExpression,       METH_VARARGS,       ""},
        {"createSymbolicVolatileExpression",    (PyCFunction)TritonContext_createSymbolicVolatileExpression,       METH_VARARGS,       ""},
        {"disassembly",                         (PyCFunction)TritonContext_disassembly,                            METH_O,             ""},
        {"enableSymbolicEngine",                (PyCFunction)TritonContext_enableSymbolicEngine,                   METH_O,             ""},
        {"enableTaintEngine",                   (PyCFunction)TritonContext_enableTaintEngine,                      METH_O,             ""},
        {"evaluateAstViaZ3",                    (PyCFunction)TritonContext_evaluateAstViaZ3,                       METH_O,             ""},
        {"getAllRegisters",                     (PyCFunction)TritonContext_getAllRegisters,                        METH_NOARGS,        ""},
        {"getArchitecture",                     (PyCFunction)TritonContext_getArchitecture,                        METH_NOARGS,        ""},
        {"getAstContext",                       (PyCFunction)TritonContext_getAstContext,                          METH_NOARGS,        ""},
        {"getAstRepresentationMode",            (PyCFunction)TritonContext_getAstRepresentationMode,               METH_NOARGS,        ""},
        {"getConcreteMemoryAreaValue",          (PyCFunction)TritonContext_getConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"getConcreteMemoryValue",              (PyCFunction)TritonContext_getConcreteMemoryValue,                 METH_O,             ""},
        {"getConcreteRegisterValue",            (PyCFunction)TritonContext_getConcreteRegisterValue,               METH_O,             ""},
        {"getConcreteVariableValue",            (PyCFunction)TritonContext_getConcreteVariableValue,               METH_O,             ""},
        {"getGprBitSize",                       (PyCFunction)TritonContext_getGprBitSize,                          METH_NOARGS,        ""},
        {"getGprSize",                          (PyCFunction)TritonContext_getGprSize,                             METH_NOARGS,        ""},
        {"getImmediateAst",                     (PyCFunction)TritonContext_getImmediateAst,                        METH_O,             ""},
        {"getMemoryAst",                        (PyCFunction)TritonContext_getMemoryAst,                           METH_O,             ""},
        {"getModel",                            (PyCFunction)TritonContext_getModel,                               METH_O,             ""},
        {"getModels",                           (PyCFunction)TritonContext_getModels,                              METH_VARARGS,       ""},
        {"getParentRegister",                   (PyCFunction)TritonContext_getParentRegister,                      METH_O,             ""},
        {"getParentRegisters",                  (PyCFunction)TritonContext_getParentRegisters,                     METH_NOARGS,        ""},
        {"getPathConstraints",                  (PyCFunction)TritonContext_getPathConstraints,                     METH_VARARGS,       ""},
        {"getPathPredicate",                    (PyCFunction)TritonContext_getPathPredicate,                       METH_VARARGS,       ""},
        {"getPredicatesToReachAddress",         (PyCFunction)TritonContext_getPredicatesToReachAddress,            METH_VARARGS,       ""},
        {"getRegister",                         (PyCFunction)TritonContext_getRegister,                            METH_O,             ""},
        {"getRegisterAst",                      (PyCFunction)TritonContext_getRegisterAst,                         METH_O,             ""},
        {"getSymbolicExpression",               (PyCFunction)TritonContext_getSymbolicExpression,                  METH_O,             ""},
        {"getSymbolicExpressions",              (PyCFunction)TritonContext_getSymbolicExpressions,                 METH_NOARGS,        ""},
        {"getSymbolicMemory",                   (PyCFunction)TritonContext_getSymbolicMemory,                      METH_VARARGS,       ""},
        {"getSymbolicMemoryValue",              (PyCFunction)TritonContext_getSymbolicMemoryValue,                 METH_O,             ""},
        {"getSymbolicRegister",                 (PyCFunction)TritonContext_getSymbolicRegister,                    METH_O,             ""},
        {"getSymbolicRegisterValue",            (PyCFunction)TritonContext_getSymbolicRegisterValue,               METH_O,             ""},
        {"getSymbolicRegisters",                (PyCFunction)TritonContext_getSymbolicRegisters,                   METH_NOARGS,        ""},
        {"getSymbolicVariable",                 (PyCFunction)TritonContext_getSymbolicVariable,                    METH_O,             ""},
        {"getSymbolicVariables",                (PyCFunction)TritonContext_getSymbolicVariables,                   METH_NOARGS,        ""},
        {"getTaintedMemory",                    (PyCFunction)TritonContext_getTaintedMemory,                       METH_NOARGS,        ""},
        {"getTaintedRegisters",                 (PyCFunction)TritonContext_getTaintedRegisters,                    METH_NOARGS,        ""},
        {"getTaintedSymbolicExpressions",       (PyCFunction)TritonContext_getTaintedSymbolicExpressions,          METH_NOARGS,        ""},
        {"isArchitectureValid",                 (PyCFunction)TritonContext_isArchitectureValid,                    METH_NOARGS,        ""},
        {"isConcreteMemoryValueDefined",        (PyCFunction)TritonContext_isConcreteMemoryValueDefined,           METH_VARARGS,       ""},
        {"isFlag",                              (PyCFunction)TritonContext_isFlag,                                 METH_O,             ""},
        {"isMemorySymbolized",                  (PyCFunction)TritonContext_isMemorySymbolized,                     METH_O,             ""},
        {"isMemoryTainted",                     (PyCFunction)TritonContext_isMemoryTainted,                        METH_O,             ""},
        {"isModeEnabled",                       (PyCFunction)TritonContext_isModeEnabled,                          METH_O,             ""},
        {"isRegister",                          (PyCFunction)TritonContext_isRegister,                             METH_O,             ""},
        {"isRegisterSymbolized",                (PyCFunction)TritonContext_isRegisterSymbolized,                   METH_O,             ""},
        {"isRegisterTainted",                   (PyCFunction)TritonContext_isRegisterTainted,                      METH_O,             ""},
        {"isRegisterValid",                     (PyCFunction)TritonContext_isRegisterValid,                        METH_O,             ""},
        {"isSat",                               (PyCFunction)TritonContext_isSat,                                  METH_O,             ""},
        {"isSymbolicEngineEnabled",             (PyCFunction)TritonContext_isSymbolicEngineEnabled,                METH_NOARGS,        ""},
        {"isSymbolicExpressionExists",          (PyCFunction)TritonContext_isSymbolicExpressionExists,             METH_O,             ""},
        {"isTaintEngineEnabled",                (PyCFunction)TritonContext_isTaintEngineEnabled,                   METH_NOARGS,        ""},
        {"isThumb",                             (PyCFunction)TritonContext_isThumb,                                METH_NOARGS,        ""},
        {"newSymbolicExpression",               (PyCFunction)TritonContext_newSymbolicExpression,                  METH_VARARGS,       ""},
        {"newSymbolicVariable",                 (PyCFunction)TritonContext_newSymbolicVariable,                    METH_VARARGS,       ""},
        {"popPathConstraint",                   (PyCFunction)TritonContext_popPathConstraint,                      METH_VARARGS,       ""},
        {"printSlicedExpressions",              (PyCFunction)TritonContext_printSlicedExpressions,                 METH_VARARGS,       ""},
        {"processing",                          (PyCFunction)TritonContext_processing,                             METH_O,             ""},
        {"pushPathConstraint",                  (PyCFunction)TritonContext_pushPathConstraint,                     METH_VARARGS,       ""},
        {"removeCallback",                      (PyCFunction)TritonContext_removeCallback,                         METH_VARARGS,       ""},
        {"reset",                               (PyCFunction)TritonContext_reset,                                  METH_NOARGS,        ""},
        {"setArchitecture",                     (PyCFunction)TritonContext_setArchitecture,                        METH_O,             ""},
        {"setAstRepresentationMode",            (PyCFunction)TritonContext_setAstRepresentationMode,               METH_O,             ""},
        {"setConcreteMemoryAreaValue",          (PyCFunction)TritonContext_setConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"setConcreteMemoryValue",              (PyCFunction)TritonContext_setConcreteMemoryValue,                 METH_VARARGS,       ""},
        {"setConcreteRegisterValue",            (PyCFunction)TritonContext_setConcreteRegisterValue,               METH_VARARGS,       ""},
        {"setConcreteVariableValue",            (PyCFunction)TritonContext_setConcreteVariableValue,               METH_VARARGS,       ""},
        {"setMode",                             (PyCFunction)TritonContext_setMode,                                METH_VARARGS,       ""},
        {"setTaintMemory",                      (PyCFunction)TritonContext_setTaintMemory,                         METH_VARARGS,       ""},
        {"setTaintRegister",                    (PyCFunction)TritonContext_setTaintRegister,                       METH_VARARGS,       ""},
        {"setThumb",                            (PyCFunction)TritonContext_setThumb,                               METH_O,             ""},
        {"simplify",                            (PyCFunction)TritonContext_simplify,                               METH_VARARGS,       ""},
        {"sliceExpressions",                    (PyCFunction)TritonContext_sliceExpressions,                       METH_O,             ""},
        {"symbolizeExpression",                 (PyCFunction)TritonContext_symbolizeExpression,                    METH_VARARGS,       ""},
        {"symbolizeMemory",                     (PyCFunction)TritonContext_symbolizeMemory,                        METH_VARARGS,       ""},
        {"symbolizeRegister",                   (PyCFunction)TritonContext_symbolizeRegister,                      METH_VARARGS,       ""},
        {"taintAssignment",                     (PyCFunction)TritonContext_taintAssignment,                        METH_VARARGS,       ""},
        {"taintMemory",                         (PyCFunction)TritonContext_taintMemory,                            METH_O,             ""},
        {"taintRegister",                       (PyCFunction)TritonContext_taintRegister,                          METH_O,             ""},
        {"taintUnion",                          (PyCFunction)TritonContext_taintUnion,                             METH_VARARGS,       ""},
        {"untaintMemory",                       (PyCFunction)TritonContext_untaintMemory,                          METH_O,             ""},
        {"untaintRegister",                     (PyCFunction)TritonContext_untaintRegister,                        METH_O,             ""},
        {nullptr,                               nullptr,                                                           0,                  nullptr}
      };


      //! Description of the python representation of a TritonContext
      PyTypeObject TritonContext_Type = {
        PyVarObject_HEAD_INIT(&PyType_Type, 0)
        "TritonContext",                            /* tp_name */
        sizeof(TritonContext_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)TritonContext_dealloc,          /* tp_dealloc */
        0,                                          /* tp_print or tp_vectorcall_offset */
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
        (getattrofunc)TritonContext_getattro,       /* tp_getattro */
        0,                                          /* tp_setattro */
        0,                                          /* tp_as_buffer */
        Py_TPFLAGS_DEFAULT,                         /* tp_flags */
        "TritonContext objects",                    /* tp_doc */
        0,                                          /* tp_traverse */
        0,                                          /* tp_clear */
        0,                                          /* tp_richcompare */
        0,                                          /* tp_weaklistoffset */
        0,                                          /* tp_iter */
        0,                                          /* tp_iternext */
        TritonContext_callbacks,                    /* tp_methods */
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
        #if IS_PY3
        0,                                          /* tp_version_tag */
        0,                                          /* tp_finalize */
        #if IS_PY3_8
        0,                                          /* tp_vectorcall */
        0,                                          /* bpo-37250: kept for backwards compatibility in CPython 3.8 only */
        #endif
        #else
        0                                           /* tp_version_tag */
        #endif
      };


      PyObject* PyTritonContext(void) {
        PyType_Ready(&TritonContext_Type);
        TritonContext_Object* object = PyObject_NEW(TritonContext_Object, &TritonContext_Type);

        if (object != nullptr) {
          object->api = new triton::API();
          object->ref = false;
          object->regAttr = nullptr;
        }

        return (PyObject*)object;
      }


      PyObject* PyTritonContext(triton::arch::architecture_e arch) {
        PyType_Ready(&TritonContext_Type);
        TritonContext_Object* object = PyObject_NEW(TritonContext_Object, &TritonContext_Type);

        if (object != nullptr) {
          object->api = new triton::API(arch);
          object->ref = false;
          object->regAttr = nullptr;
        }

        return (PyObject*)object;
      }


      PyObject* PyTritonContextRef(triton::API& api) {
        PyType_Ready(&TritonContext_Type);
        TritonContext_Object* object = PyObject_NEW(TritonContext_Object, &TritonContext_Type);

        if (object != nullptr) {
          object->api = &api;
          object->ref = true;
          object->regAttr = nullptr;
        }

        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
