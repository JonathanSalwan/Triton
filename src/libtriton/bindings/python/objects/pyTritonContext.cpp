//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/api.hpp>
#include <triton/exceptions.hpp>
#include <triton/register.hpp>



/*! \page py_TritonContext_page TritonContext
    \brief [**python api**] All information about the Triton Context class
    \anchor tritonContext

\section triton_py_description Description
<hr>

The libTriton offers Python bindings on its C++ API which allow you to build analysis in Python as well as in C++.

~~~~~~~~~~~~~{.py}
>>> from triton import TritonContext, ARCH
>>>
>>> ctx = TritonContext()
>>> ctx.setArchitecture(ARCH.X86_64)

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
The symbolic expression (`symExpr`) must be aligned to the targeted size register. E.g: for SSE registers, the expression must be aligned
to 128-bits. Otherwise, you will probably get a sort mismatch error when you will solve the expression. If you want to assign an
expression to a sub-register like `AX`, `AH` or `AL`, please, craft your expression with the `concat()` and `extract()` ast functions.

- <b>bool buildSemantics(\ref py_Instruction_page inst)</b><br>
Builds the instruction semantics. Returns true if the instruction is supported. You must define an architecture before.

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

- <b>void concretizeRegister(\ref py_Register_page reg)</b><br>
Concretizes a specific symbolic register reference.

- <b>\ref py_SymbolicVariable_page convertExpressionToSymbolicVariable(integer symExprId, integer symVarSize, string comment)</b><br>
Converts a symbolic expression to a symbolic variable. `symVarSize` must be in bits. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page convertMemoryToSymbolicVariable(\ref py_MemoryAccess_page mem, string comment)</b><br>
Converts a symbolic memory expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicVariable_page convertRegisterToSymbolicVariable(\ref py_Register_page reg, string comment)</b><br>
Converts a symbolic register expression to a symbolic variable. This function returns the new symbolic variable created.

- <b>\ref py_SymbolicExpression_page createSymbolicFlagExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_Register_page flag, string comment)</b><br>
Returns the new symbolic register expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicMemoryExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_MemoryAccess_page mem, string comment)</b><br>
Returns the new symbolic memory expression and links this expression to the instruction.

- <b>\ref py_SymbolicExpression_page createSymbolicRegisterExpression(\ref py_Instruction_page inst, \ref py_AstNode_page node, \ref py_Register_page reg, string comment)</b><br>
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

- <b>\ref py_AstContext_page getAstContext(void)</b><br>
Returns the AST context to create and modify nodes.

- <b>\ref py_AST_REPRESENTATION_page getAstRepresentationMode(void)</b><br>
Returns the current AST representation mode.

- <b>bytes getConcreteMemoryAreaValue(integer baseAddr, integer size)</b><br>
Returns the concrete value of a memory area.

- <b>integer getConcreteMemoryValue(intger addr)</b><br>
Returns the concrete value of a memory cell.

- <b>integer getConcreteMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the concrete value of memory cells.

- <b>integer getConcreteRegisterValue(\ref py_Register_page reg)</b><br>
Returns the concrete value of a register.

- <b>integer getConcreteVariableValue(\ref py_SymbolicVariable_page symVar)</b><br>
Returns the concrete value of a symbolic variable.

- <b>integer getGprBitSize(void)</b><br>
Returns the size in bit of the General Purpose Registers.

- <b>integer getGprSize(void)</b><br>
Returns the size in byte of the General Purpose Registers.

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

- <b>[\ref py_PathConstraint_page, ...] getPathConstraints(void)</b><br>
Returns the logical conjunction vector of path constraints as list of \ref py_PathConstraint_page.

- <b>\ref py_AstNode_page getPathConstraintsAst(void)</b><br>
Returns the logical conjunction AST of path constraints.

- <b>\ref py_Register_page getRegister(\ref py_REG_page id)</b><br>
Returns the \ref py_Register_page class corresponding to a \ref py_REG_page id.

- <b>\ref py_AstNode_page getRegisterAst(\ref py_Register_page reg)</b><br>
Returns the AST corresponding to the \ref py_Register_page with the SSA form.

- <b>\ref py_SymbolicExpression_page getSymbolicExpressionFromId(intger symExprId)</b><br>
Returns the symbolic expression corresponding to an id.

- <b>dict getSymbolicExpressions(void)</b><br>
Returns all symbolic expressions as a dictionary of {integer SymExprId : \ref py_SymbolicExpression_page expr}.

- <b>dict getSymbolicMemory(void)</b><br>
Returns the map of symbolic memory as {integer address : \ref py_SymbolicExpression_page expr}.

- <b>\ref py_SymbolicExpression_page getSymbolicMemory(intger addr)</b><br>
Returns the \ref py_SymbolicExpression_page corresponding to a memory address.

- <b>integer getSymbolicMemoryValue(intger addr)</b><br>
Returns the symbolic memory value.

- <b>integer getSymbolicMemoryValue(\ref py_MemoryAccess_page mem)</b><br>
Returns the symbolic memory value.

- <b>dict getSymbolicRegisters(void)</b><br>
Returns the map of symbolic register as {\ref py_REG_page reg : \ref py_SymbolicExpression_page expr}.

- <b>\ref py_SymbolicExpression_page getSymbolicRegister(\ref py_Register_page reg)</b><br>
Returns the \ref py_SymbolicExpression_page corresponding to the parent register.

- <b>integer getSymbolicRegisterValue(\ref py_Register_page reg)</b><br>
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

- <b>bool isFlag(\ref py_Register_page reg)</b><br>
Returns true if the register is a flag.

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

- <b>void reset(void)</b><br>
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

- <b>void setConcreteMemoryValue(\ref py_MemoryAccess_page mem, integer value)</b><br>
Sets the concrete value of memory cells. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteRegisterValue(\ref py_Register_page reg, integer value)</b><br>
Sets the concrete value of a register. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteVariableValue(\ref py_SymbolicVariable_page symVar, integer value)</b><br>
Sets the concrete value of a symbolic variable.

- <b>bool setTaintMemory(\ref py_MemoryAccess_page mem, bool flag)</b><br>
Sets the targeted memory as tainted or not. Returns true if the memory is still tainted.

- <b>bool setTaintRegister(\ref py_Register_page reg, bool flag)</b><br>
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

- <b>bool taintAssignmentMemoryRegister(\ref py_MemoryAccess_page memDst, \ref py_Register_page regSrc)</b><br>
Taints `memDst` from `regSrc` with an assignment - `memDst` is tainted if `regSrc` is tainted, otherwise
`memDst` is untained. Return true if `memDst` is tainted.

- <b>bool taintAssignmentRegisterImmediate(\ref py_Register_page regDst)</b><br>
Taints `regDst` with an assignment - `regDst` is untained. Returns true if `reDst` is still tainted.

- <b>bool taintAssignmentRegisterMemory(\ref py_Register_page regDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `regDst` from `MemSrc` with an assignment - `regDst` is tainted if `memSrc` is tainted, otherwise
`regDst` is untained. Return true if `regDst` is tainted.

- <b>bool taintAssignmentRegisterRegister(\ref py_Register_page regDst, \ref py_Register_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an assignment - `regDst` is tainted if `regSrc` is tainted, otherwise
`regDst` is untained. Return true if `regDst` is tainted.

- <b>bool taintMemory(intger addr)</b><br>
Taints an address. Returns true if the address is tainted.

- <b>bool taintMemory(\ref py_MemoryAccess_page mem)</b><br>
Taints a memory. Returns true if the memory is tainted.

- <b>bool taintRegister(\ref py_Register_page reg)</b><br>
Taints a register. Returns true if the register is tainted.

- <b>bool taintUnionMemoryImmediate(\ref py_MemoryAccess_page memDst)</b><br>
Taints `memDst` with an union - `memDst` does not changes. Returns true if `memDst` is tainted.

- <b>bool taintUnionMemoryMemory(\ref py_MemoryAccess_page memDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `memDst` from `memSrc` with an union - `memDst` is tainted if `memDst` or `memSrc` are
tainted. Returns true if `memDst` is tainted.

- <b>bool taintUnionMemoryRegister(\ref py_MemoryAccess_page memDst, \ref py_Register_page regSrc)</b><br>
Taints `memDst` from `RegSrc` with an union - `memDst` is tainted if `memDst` or `regSrc` are
tainted. Returns true if `memDst` is tainted.

- <b>bool taintUnionRegisterImmediate(\ref py_Register_page regDst)</b><br>
Taints `regDst` with an union - `regDst` does not changes. Returns true if `regDst` is tainted.

- <b>bool taintUnionRegisterMemory(\ref py_Register_page regDst, \ref py_MemoryAccess_page memSrc)</b><br>
Taints `regDst` from `memSrc` with an union - `regDst` is tainted if `regDst` or `memSrc` are
tainted. Returns true if `regDst` is tainted.

- <b>bool taintUnionRegisterRegister(\ref py_Register_page regDst, \ref py_Register_page regSrc)</b><br>
Taints `regDst` from `regSrc` with an union - `regDst` is tainted if `regDst` or `regSrc` are
tainted. Returns true if `regDst` is tainted.

- <b>void unmapMemory(integer baseAddr, integer size=1)</b><br>
Removes the range `[baseAddr:size]` from the internal memory representation.

- <b>\ref py_AstNode_page unrollAst(\ref py_AstNode_page node)</b><br>
Unrolls the SSA form of a given AST.

- <b>bool untaintMemory(intger addr)</b><br>
Untaints an address. Returns true if the address is still tainted.

- <b>bool untaintMemory(\ref py_MemoryAccess_page mem)</b><br>
Untaints a memory. Returns true if the memory is still tainted.

- <b>bool untaintRegister(\ref py_Register_page reg)</b><br>
Untaints a register. Returns true if the register is still tainted.

*/



namespace triton {
  namespace bindings {
    namespace python {

#ifdef IS_PY3
      NAMESPACE_TYPE(registers, TritonRegisters)
      PyAPI_DATA(PyTypeObject) Instruction_Type;
#endif

      static void TritonContext_dealloc(PyObject* self) {
        if (((TritonContext_Object*)self)->ref == false)
          delete PyTritonContext_AsTritonContext(self);
        Py_XDECREF(((TritonContext_Object*)self)->regAttr);
        Py_TYPE(self)->tp_free((PyObject*)self);
      }


      static void TritonContext_fillRegistersAttribute(PyObject* self) {
        /* Fill self->regAttr */
        auto& regs = PyTritonContext_AsTritonContext(self)->getAllRegisters();

#ifdef IS_PY3
        PyType_Ready(&TritonRegisters_Type);
        PyObject* registersDict = TritonRegisters_Type.tp_dict;
#else
        PyObject* registersDict = xPyDict_New();
#endif
        for (auto& reg : regs)
          xPyDict_SetItem(registersDict, PyString_FromString(reg.second.getName().c_str()), PyRegister(reg.second));

        Py_XDECREF(((TritonContext_Object*)(self))->regAttr);
#ifdef IS_PY3
        ((TritonContext_Object*)(self))->regAttr = _PyObject_New(&TritonRegisters_Type);
#else
        ((TritonContext_Object*)(self))->regAttr = xPyClass_New(nullptr, registersDict, xPyString_FromString("registers"));
#endif
      }


      static PyObject* TritonContext_addCallback(PyObject* self, PyObject* args) {
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;
        PyObject* cb       = nullptr;
        PyObject* cb_self  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &function, &mode);

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "addCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "addCallback(): Expects a CALLBACK as second argument.");

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
                  PyObject* type      = nullptr;
                  PyObject* value     = nullptr;
                  PyObject* traceback = nullptr;

                  /* Fetch the last exception */
                  PyErr_Fetch(&type, &value, &traceback);

                  std::string str = PyString_AsString(PyObject_Str(value));
                  Py_XDECREF(type);
                  Py_XDECREF(value);
                  Py_XDECREF(traceback);
                  throw triton::exceptions::Callbacks(str);
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
                  PyObject* type      = nullptr;
                  PyObject* value     = nullptr;
                  PyObject* traceback = nullptr;

                  /* Fetch the last exception */
                  PyErr_Fetch(&type, &value, &traceback);

                  std::string str = PyString_AsString(PyObject_Str(value));
                  Py_XDECREF(type);
                  Py_XDECREF(value);
                  Py_XDECREF(traceback);
                  throw triton::exceptions::Callbacks(str);
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
                  PyObject* type      = nullptr;
                  PyObject* value     = nullptr;
                  PyObject* traceback = nullptr;

                  /* Fetch the last exception */
                  PyErr_Fetch(&type, &value, &traceback);

                  std::string str = PyString_AsString(PyObject_Str(value));
                  Py_XDECREF(type);
                  Py_XDECREF(value);
                  Py_XDECREF(traceback);
                  throw triton::exceptions::Callbacks(str);
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
                  PyObject* type      = nullptr;
                  PyObject* value     = nullptr;
                  PyObject* traceback = nullptr;

                  /* Fetch the last exception */
                  PyErr_Fetch(&type, &value, &traceback);

                  std::string str = PyString_AsString(PyObject_Str(value));
                  Py_XDECREF(type);
                  Py_XDECREF(value);
                  Py_XDECREF(traceback);
                  throw triton::exceptions::Callbacks(str);
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
                  PyObject* type      = nullptr;
                  PyObject* value     = nullptr;
                  PyObject* traceback = nullptr;

                  /* Fetch the last exception */
                  PyErr_Fetch(&type, &value, &traceback);

                  std::string str = PyString_AsString(PyObject_Str(value));
                  Py_XDECREF(type);
                  Py_XDECREF(value);
                  Py_XDECREF(traceback);
                  throw triton::exceptions::Callbacks(str);
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
        PyArg_ParseTuple(args, "|OO", &se, &mem);

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Expects a SymbolicExpression as first argument.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Expects a MemoryAccess as second argument.");

        const triton::engines::symbolic::SharedSymbolicExpression& arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::MemoryAccess arg2 = *PyMemoryAccess_AsMemoryAccess(mem);

        try {
          PyTritonContext_AsTritonContext(self)->assignSymbolicExpressionToMemory(arg1, arg2);
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
        PyArg_ParseTuple(args, "|OO", &se, &reg);

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a SymbolicExpression as first argument.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a Register as second argument.");

        const triton::engines::symbolic::SharedSymbolicExpression& arg1 = PySymbolicExpression_AsSymbolicExpression(se);
        triton::arch::Register arg2 = *PyRegister_AsRegister(reg);

        try {
          PyTritonContext_AsTritonContext(self)->assignSymbolicExpressionToRegister(arg1, arg2);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_buildSemantics(PyObject* self, PyObject* inst) {
        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "buildSemantics(): Expects an Instruction as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->buildSemantics(*PyInstruction_AsInstruction(inst)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_clearPathConstraints(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->clearPathConstraints();
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
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }
        }

        /* If mem is a MemoryAccess */
        else if (PyMemoryAccess_Check(mem)) {
          try {
            PyTritonContext_AsTritonContext(self)->concretizeMemory(*PyMemoryAccess_AsMemoryAccess(mem));
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


      static PyObject* TritonContext_concretizeRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "concretizeRegister(): Expects a Register as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->concretizeRegister(*PyRegister_AsRegister(reg));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_convertExpressionToSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* exprId        = nullptr;
        PyObject* symVarSize    = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOO", &exprId, &symVarSize, &comment);

        if (exprId == nullptr || (!PyLong_Check(exprId) && !PyInt_Check(exprId)))
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Expects an integer as first argument.");

        if (symVarSize == nullptr || (!PyLong_Check(symVarSize) && !PyInt_Check(symVarSize)))
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Expects an integer as second argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertExpressionToSymbolicVariable(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->convertExpressionToSymbolicVariable(PyLong_AsUsize(exprId), PyLong_AsUint32(symVarSize), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_convertMemoryToSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* mem           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &comment);

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "convertMemoryToSymbolicVariable(): Expects a MemoryAccess as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertMemoryToSymbolicVariable(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->convertMemoryToSymbolicVariable(*PyMemoryAccess_AsMemoryAccess(mem), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_convertRegisterToSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* reg           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &comment);

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "convertRegisterToSymbolicVariable(): Expects a Register as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "convertRegisterToSymbolicVariable(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->convertRegisterToSymbolicVariable(*PyRegister_AsRegister(reg), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_createSymbolicFlagExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* flag          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOOO", &inst, &node, &flag, &comment);

#ifdef IS_PY3
        if (inst == nullptr || (Py_TYPE(inst) == &Instruction_Type))
#else
        if (inst == nullptr || (!PyInstance_Check(inst)))
#endif
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a AstNode as second argument.");

        if (flag == nullptr || (!PyRegister_Check(flag)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a Register as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);
        triton::arch::Register arg3 = *PyRegister_AsRegister(flag);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicFlagExpression(arg1, arg2, arg3, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_createSymbolicMemoryExpression(PyObject* self, PyObject* args) {
        PyObject* inst          = nullptr;
        PyObject* node          = nullptr;
        PyObject* mem           = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OOOO", &inst, &node, &mem, &comment);

#ifdef IS_PY3
        if (inst == nullptr || (Py_TYPE(inst) == &Instruction_Type))
#else
        if (inst == nullptr || (!PyInstance_Check(inst)))
#endif
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
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);
        triton::arch::MemoryAccess arg3 = *PyMemoryAccess_AsMemoryAccess(mem);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicMemoryExpression(arg1, arg2, arg3, ccomment));
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
        PyArg_ParseTuple(args, "|OOOO", &inst, &node, &reg, &comment);

#ifdef IS_PY3
        if (inst == nullptr || (Py_TYPE(inst) == &Instruction_Type))
#else
        if (inst == nullptr || (!PyInstance_Check(inst)))
#endif
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a AstNode as second argument.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a Register as third argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Expects a sting as fourth argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);
        triton::arch::Register arg3 = *PyRegister_AsRegister(reg);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicRegisterExpression(arg1, arg2, arg3, ccomment));
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
        PyArg_ParseTuple(args, "|OOO", &inst, &node, &comment);

#ifdef IS_PY3
        if (inst == nullptr || (Py_TYPE(inst) == &Instruction_Type))
#else
        if (inst == nullptr || (!PyInstance_Check(inst)))
#endif
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects an Instruction as first argument.");

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects a AstNode as second argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Expects a sting as third argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        triton::arch::Instruction arg1 = *PyInstruction_AsInstruction(inst);
        triton::ast::SharedAbstractNode arg2 = PyAstNode_AsAstNode(node);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicVolatileExpression(arg1, arg2, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_disassembly(PyObject* self, PyObject* inst) {
        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "disassembly(): Expects an Instruction as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->disassembly(*PyInstruction_AsInstruction(inst));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_enableMode(PyObject* self, PyObject* args) {
        PyObject* mode = nullptr;
        PyObject* flag = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mode, &flag);

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "enableMode(): Expects a MODE as argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "enableMode(): Expects an boolean flag as second argument.");

        try {
          PyTritonContext_AsTritonContext(self)->enableMode(static_cast<enum triton::modes::mode_e>(PyLong_AsUint32(mode)), PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_enableSymbolicEngine(PyObject* self, PyObject* flag) {
        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "enableSymbolicEngine(): Expects an boolean as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->enableSymbolicEngine(PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_enableTaintEngine(PyObject* self, PyObject* flag) {
        if (!PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "enableTaintEngine(): Expects an boolean as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->enableTaintEngine(PyLong_AsBool(flag));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_evaluateAstViaZ3(PyObject* self, PyObject* node) {
        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "evaluateAstViaZ3(): Expects a AstNode as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->evaluateAstViaZ3(PyAstNode_AsAstNode(node)));
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getArchitecture(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getArchitecture());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getAstContext(PyObject* self, PyObject* noarg) {
        try {
          return PyAstContext(PyTritonContext_AsTritonContext(self)->getAstContext());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getAstRepresentationMode(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getAstRepresentationMode());
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
        PyArg_ParseTuple(args, "|OO", &addr, &size);

        try {
          std::vector<triton::uint8> vv = PyTritonContext_AsTritonContext(self)->getConcreteMemoryAreaValue(PyLong_AsUint64(addr), PyLong_AsUsize(size));
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


      static PyObject* TritonContext_getConcreteMemoryValue(PyObject* self, PyObject* mem) {
        try {
          if (PyLong_Check(mem) || PyInt_Check(mem))
              return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteMemoryValue(PyLong_AsUint64(mem)));
          else if (PyMemoryAccess_Check(mem))
              return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
          else
            return PyErr_Format(PyExc_TypeError, "getConcreteMemoryValue(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getConcreteRegisterValue(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getConcreteRegisterValue(): Expects a Register as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getConcreteVariableValue(PyObject* self, PyObject* symVar) {
        if (!PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "getConcreteVariableValue(): Expects a SymbolicVariable as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteVariableValue(PySymbolicVariable_AsSymbolicVariable(symVar)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getGprBitSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getGprBitSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getGprSize(PyObject* self, PyObject* noarg) {
        try {
          return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getGprSize());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getImmediateAst(PyObject* self, PyObject* imm) {
        if (!PyImmediate_Check(imm))
          return PyErr_Format(PyExc_TypeError, "getImmediateAst(): Expects an Immediate as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getImmediateAst(*PyImmediate_AsImmediate(imm)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getMemoryAst(PyObject* self, PyObject* mem) {
        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "getMemoryAst(): Expects an MemoryAccess as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getMemoryAst(*PyMemoryAccess_AsMemoryAccess(mem)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getModel(PyObject* self, PyObject* node) {
        PyObject* ret = nullptr;

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModel(): Expects a AstNode as argument.");

        try {
          ret = xPyDict_New();
          auto model = PyTritonContext_AsTritonContext(self)->getModel(PyAstNode_AsAstNode(node));
          for (auto it = model.begin(); it != model.end(); it++) {
            xPyDict_SetItem(ret, PyLong_FromUint32(it->first), PySolverModel(it->second));
          }
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
        PyArg_ParseTuple(args, "|OO", &node, &limit);

        if (node == nullptr || !PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModels(): Expects a AstNode as first argument.");

        if (limit == nullptr || (!PyLong_Check(limit) && !PyInt_Check(limit)))
          return PyErr_Format(PyExc_TypeError, "getModels(): Expects an integer as second argument.");

        try {
          auto models = PyTritonContext_AsTritonContext(self)->getModels(PyAstNode_AsAstNode(node), PyLong_AsUint32(limit));
          triton::uint32 index = 0;

          ret = xPyList_New(models.size());
          for (auto it = models.begin(); it != models.end(); it++) {
            PyObject* mdict = xPyDict_New();
            auto model = *it;

            for (auto it2 = model.begin(); it2 != model.end(); it2++) {
              xPyDict_SetItem(mdict, PyLong_FromUint32(it2->first), PySolverModel(it2->second));
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getPathConstraints(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        try {
          triton::uint32 index = 0;
          const std::vector<triton::engines::symbolic::PathConstraint>& pc = PyTritonContext_AsTritonContext(self)->getPathConstraints();
          ret = xPyList_New(pc.size());

          for (auto it = pc.begin(); it != pc.end(); it++)
            PyList_SetItem(ret, index++, PyPathConstraint(*it));

          return ret;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getPathConstraintsAst(PyObject* self, PyObject* noarg) {
        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getPathConstraintsAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getRegister(PyObject* self, PyObject* regIn) {
        triton::arch::registers_e rid = triton::arch::ID_REG_INVALID;

        if (regIn == nullptr || (!PyLong_Check(regIn) && !PyInt_Check(regIn)))
          return PyErr_Format(PyExc_TypeError, "getRegister(): Expects an id as argument.");

        try {
          rid = static_cast<triton::arch::registers_e>(PyLong_AsUint32(regIn));
          triton::arch::Register regOut(PyTritonContext_AsTritonContext(self)->getRegister(rid));
          return PyRegister(regOut);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getRegisterAst(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getRegisterAst(): Expects an Register as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getRegisterAst(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicExpressionFromId(PyObject* self, PyObject* symExprId) {
        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getSymbolicExpressionFromId(): Expects an integer as argument.");

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->getSymbolicExpressionFromId(PyLong_AsUsize(symExprId)));
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicMemory(PyObject* self, PyObject* args) {
        PyObject* ret  = nullptr;
        PyObject* addr = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|O", &addr);

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
            return PyErr_Format(PyExc_TypeError, "getSymbolicMemory(): Expects an integer or nothing as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicMemoryValue(PyObject* self, PyObject* mem) {
        if (!PyLong_Check(mem) && !PyInt_Check(mem) && !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryValue(): Expects an integer or a MemoryAccess as argument.");

        try {
          if (PyLong_Check(mem) || PyInt_Check(mem))
            return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getSymbolicMemoryValue(PyLong_AsUint64(mem)));
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getSymbolicMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegister(): Expects a Register as argument.");

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->getSymbolicRegister(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicRegisterValue(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterValue(): Expects a Register as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getSymbolicRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicVariableFromId(PyObject* self, PyObject* symVarId) {
        if (!PyLong_Check(symVarId) && !PyInt_Check(symVarId))
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromId(): Expects an integer as argument.");

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->getSymbolicVariableFromId(PyLong_AsUsize(symVarId)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicVariableFromName(PyObject* self, PyObject* symVarName) {
        if (!PyString_Check(symVarName))
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromName(): Expects a string as argument.");

        try {
          std::string arg = PyString_AsString(symVarName);
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->getSymbolicVariableFromName(arg));
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getTaintedMemory(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        try {
          std::set<triton::uint64> addresses = PyTritonContext_AsTritonContext(self)->getTaintedMemory();

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


      static PyObject* TritonContext_getTaintedRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        try {
          std::set<const triton::arch::Register*> registers = PyTritonContext_AsTritonContext(self)->getTaintedRegisters();

          size = registers.size();
          ret = xPyList_New(size);
          for (const auto* reg: registers) {
            PyList_SetItem(ret, index, PyRegister(*reg));
            index++;
          }
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isFlag(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isFlag(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isFlag(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isMemoryMapped(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;
        triton::uint64 c_baseAddr = 0;
        triton::usize c_size      = 1;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &baseAddr, &size);

        if (baseAddr == nullptr || (!PyLong_Check(baseAddr) && !PyInt_Check(baseAddr)))
          return PyErr_Format(PyExc_TypeError, "isMemoryMapped(): Expects a base address (integer) as first argument.");

        if (size != nullptr && !PyLong_Check(size) && !PyInt_Check(size))
          return PyErr_Format(PyExc_TypeError, "isMemoryMapped(): Expects a size (integer) as second argument.");

        try {
          c_baseAddr = PyLong_AsUint64(baseAddr);
          if (size != nullptr)
            c_size = PyLong_AsUsize(size);
          if (PyTritonContext_AsTritonContext(self)->isMemoryMapped(c_baseAddr, c_size) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
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
            return PyErr_Format(PyExc_TypeError, "isMemorySymbolized(): Expects a MemoryAccess or an integer as argument.");
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
            return PyErr_Format(PyExc_TypeError, "isMemoryTainted(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegister(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isRegisterSymbolized(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterSymbolized(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegisterSymbolized(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isRegisterTainted(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterTainted(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegisterTainted(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isRegisterValid(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterValid(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isRegisterValid(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isSat(PyObject* self, PyObject* node) {
        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "isSat(): Expects a AstNode as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isSat(PyAstNode_AsAstNode(node)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isSymbolicExpressionIdExists(PyObject* self, PyObject* symExprId) {
        if (!PyInt_Check(symExprId) && !PyLong_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Expects an integer as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isSymbolicExpressionIdExists(PyLong_AsUsize(symExprId)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_isModeEnabled(PyObject* self, PyObject* mode) {
        if (!PyInt_Check(mode) && !PyLong_Check(mode))
          return PyErr_Format(PyExc_TypeError, "isModeEnabled(): Expects a MODE as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->isModeEnabled(static_cast<enum triton::modes::mode_e>(PyLong_AsUint32(mode))) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
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
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_newSymbolicExpression(PyObject* self, PyObject* args) {
        PyObject* node          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &comment);

        if (node == nullptr || (!PyAstNode_Check(node)))
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Expects a AstNode as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Expects a sting as second argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->newSymbolicExpression(PyAstNode_AsAstNode(node), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_newSymbolicVariable(PyObject* self, PyObject* args) {
        PyObject* size        = nullptr;
        PyObject* comment     = nullptr;
        std::string ccomment  = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &size, &comment);

        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "newSymbolicVariable(): Expects an integer as first argument.");

        if (comment != nullptr && !PyString_Check(comment))
          return PyErr_Format(PyExc_TypeError, "newSymbolicVariable(): Expects a sting as second  argument.");

        if (comment != nullptr)
          ccomment = PyString_AsString(comment);

        try {
          return PySymbolicVariable(PyTritonContext_AsTritonContext(self)->newSymbolicVariable(PyLong_AsUint32(size), ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_processing(PyObject* self, PyObject* inst) {
        if (!PyInstruction_Check(inst))
          return PyErr_Format(PyExc_TypeError, "processing(): Expects an Instruction as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->processing(*PyInstruction_AsInstruction(inst)))
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_removeAllCallbacks(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->removeAllCallbacks();
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
        PyArg_ParseTuple(args, "|OO", &function, &mode);

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Expects a CALLBACK as second argument.");

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
              return PyErr_Format(PyExc_TypeError, "removeCallback(): Invalid kind of callback.");
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        /* Free cb if exists */
        if (PyMethod_Check(function))
          Py_DECREF(cb);

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_reset(PyObject* self, PyObject* noarg) {
        try {
          PyTritonContext_AsTritonContext(self)->reset();
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setArchitecture(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "setArchitecture(): Expects an ARCH as argument.");

        try {
          /* Set the architecture */
          PyTritonContext_AsTritonContext(self)->setArchitecture(static_cast<enum triton::arch::architectures_e>(PyLong_AsUint32(arg)));
          TritonContext_fillRegistersAttribute(self);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_setAstRepresentationMode(PyObject* self, PyObject* arg) {
        if (!PyLong_Check(arg) && !PyInt_Check(arg))
          return PyErr_Format(PyExc_TypeError, "setArcsetAstRepresentationMode(): Expects an AST_REPRESENTATION as argument.");

        try {
          PyTritonContext_AsTritonContext(self)->setAstRepresentationMode(PyLong_AsUint32(arg));
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
        PyArg_ParseTuple(args, "|OO", &baseAddr, &values);

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
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryAreaValue(PyLong_AsUint64(baseAddr), vv);
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


      static PyObject* TritonContext_setConcreteMemoryValue(PyObject* self, PyObject* args) {
        PyObject* mem    = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &value);

        /* setConcreteMemoryValue(integer, integer) */
        if (mem != nullptr && (PyLong_Check(mem) || PyInt_Check(mem))) {
          if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
            return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Expects a value as second argument.");

          triton::uint64 addr   = PyLong_AsUint64(mem);
          triton::uint32 cvalue = PyLong_AsUint32(value);

          if (cvalue > 0xff)
            return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Value must be on 8 bits.");

          try {
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryValue(addr, static_cast<triton::uint8>(cvalue & 0xff));
          }
          catch (const triton::exceptions::Exception& e) {
            return PyErr_Format(PyExc_TypeError, "%s", e.what());
          }

        }

        /* setConcreteMemoryValue(MemoryAccess) */
        else if (mem != nullptr && PyMemoryAccess_Check(mem)) {
          if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
            return PyErr_Format(PyExc_TypeError, "setConcreteMemoryValue(): Expects a value as second argument.");
          try {
            triton::uint512 cvalue = PyLong_AsUint512(value);
            PyTritonContext_AsTritonContext(self)->setConcreteMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem), cvalue);
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


      static PyObject* TritonContext_setConcreteRegisterValue(PyObject* self, PyObject* args) {
        PyObject* reg    = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &value);

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "setConcreteRegisterValue(): Expects a Register as first argument.");

        if (value == nullptr || (!PyLong_Check(value) && !PyInt_Check(value)))
          return PyErr_Format(PyExc_TypeError, "setConcreteRegisterValue(): Expects a value as second argument.");

        try {
          triton::uint512 cvalue = PyLong_AsUint512(value);
          PyTritonContext_AsTritonContext(self)->setConcreteRegisterValue(*PyRegister_AsRegister(reg), cvalue);
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
        PyArg_ParseTuple(args, "|OO", &symVar, &value);

        if (symVar == nullptr || !PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "setConcreteVariableValue(): Bad argument type.");

        if (value == nullptr)
          return PyErr_Format(PyExc_TypeError, "setConcreteVariableValue(): Expects a second argument as integer value.");

        try {
          PyTritonContext_AsTritonContext(self)->setConcreteVariableValue(PySymbolicVariable_AsSymbolicVariable(symVar), PyLong_AsUint512(value));
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
        PyArg_ParseTuple(args, "|OO", &mem, &flag);

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "setTaintMemory(): Expects a MemoryAccess as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTaintMemory(): Expects a boolean as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->setTaintMemory(*PyMemoryAccess_AsMemoryAccess(mem), PyLong_AsBool(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_setTaintRegister(PyObject* self, PyObject* args) {
        PyObject* reg    = nullptr;
        PyObject* flag   = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &flag);

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "setTaintRegister(): Expects a Register as first argument.");

        if (flag == nullptr || !PyBool_Check(flag))
          return PyErr_Format(PyExc_TypeError, "setTaintRegister(): Expects a boolean as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->setTaintRegister(*PyRegister_AsRegister(reg), PyLong_AsBool(flag)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_simplify(PyObject* self, PyObject* args) {
        PyObject* node        = nullptr;
        PyObject* z3Flag      = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &z3Flag);

        if (node == nullptr || !PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "simplify(): Expects a AstNode as first argument.");

        if (z3Flag != nullptr && !PyBool_Check(z3Flag))
          return PyErr_Format(PyExc_TypeError, "simplify(): Expects a boolean as second argument.");

        if (z3Flag == nullptr)
          z3Flag = PyLong_FromUint32(false);

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->processSimplification(PyAstNode_AsAstNode(node), PyLong_AsBool(z3Flag)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_sliceExpressions(PyObject* self, PyObject* expr) {
        PyObject* ret = nullptr;

        if (!PySymbolicExpression_Check(expr))
          return PyErr_Format(PyExc_TypeError, "sliceExpressions(): Expects a SymbolicExpression as argument.");

        try {
          auto exprs = PyTritonContext_AsTritonContext(self)->sliceExpressions(PySymbolicExpression_AsSymbolicExpression(expr));

          ret = xPyDict_New();
          for (auto it = exprs.begin(); it != exprs.end(); it++)
            xPyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_taintAssignmentMemoryImmediate(PyObject* self, PyObject* mem) {
        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryImmediate(): Expects a MemoryAccess as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintAssignmentMemoryImmediate(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintAssignmentMemoryMemory(PyObject* self, PyObject* args) {
        PyObject* mem1 = nullptr;
        PyObject* mem2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem1, &mem2);

        if (mem1 == nullptr || !PyMemoryAccess_Check(mem1))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryMemory(): Expects a MemoryAccess as first argument.");

        if (mem2 == nullptr || !PyMemoryAccess_Check(mem2))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintAssignmentMemoryMemory(*PyMemoryAccess_AsMemoryAccess(mem1), *PyMemoryAccess_AsMemoryAccess(mem2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintAssignmentMemoryRegister(PyObject* self, PyObject* args) {
        PyObject* mem = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &reg);

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryRegister(): Expects a MemoryAccess as first argument.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryRegister(): Expects a Register as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintAssignmentMemoryRegister(*PyMemoryAccess_AsMemoryAccess(mem), *PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintAssignmentRegisterImmediate(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterImmediate(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintAssignmentRegisterImmediate(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintAssignmentRegisterMemory(PyObject* self, PyObject* args) {
        PyObject* reg = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &mem);

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterMemory(): Expects a Register as first argument.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintAssignmentRegisterMemory(*PyRegister_AsRegister(reg), *PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintAssignmentRegisterRegister(PyObject* self, PyObject* args) {
        PyObject* reg1 = nullptr;
        PyObject* reg2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg1, &reg2);

        if (reg1 == nullptr || !PyRegister_Check(reg1))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterRegister(): Expects a Register as first argument.");

        if (reg2 == nullptr || !PyRegister_Check(reg2))
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterRegister(): Expects a Register as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintAssignmentRegisterRegister(*PyRegister_AsRegister(reg1), *PyRegister_AsRegister(reg2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
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
            return PyErr_Format(PyExc_TypeError, "taintMemory(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_taintRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintRegister(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnionMemoryImmediate(PyObject* self, PyObject* mem) {
        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryImmediate(): Expects a MemoryAccess as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintUnionMemoryImmediate(*PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnionMemoryMemory(PyObject* self, PyObject* args) {
        PyObject* mem1 = nullptr;
        PyObject* mem2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem1, &mem2);

        if (mem1 == nullptr || !PyMemoryAccess_Check(mem1))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryMemory(): Expects a MemoryAccess as first argument.");

        if (mem2 == nullptr || !PyMemoryAccess_Check(mem2))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintUnionMemoryMemory(*PyMemoryAccess_AsMemoryAccess(mem1), *PyMemoryAccess_AsMemoryAccess(mem2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnionMemoryRegister(PyObject* self, PyObject* args) {
        PyObject* mem = nullptr;
        PyObject* reg = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &mem, &reg);

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryRegister(): Expects a MemoryAccess as first argument.");

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryRegister(): Expects a Register as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintUnionMemoryRegister(*PyMemoryAccess_AsMemoryAccess(mem), *PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnionRegisterImmediate(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterImmediate(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintUnionRegisterImmediate(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnionRegisterMemory(PyObject* self, PyObject* args) {
        PyObject* reg = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg, &mem);

        if (reg == nullptr || !PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterMemory(): Expects a Register as first argument.");

        if (mem == nullptr || !PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterMemory(): Expects a MemoryAccess as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintUnionRegisterMemory(*PyRegister_AsRegister(reg), *PyMemoryAccess_AsMemoryAccess(mem)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_taintUnionRegisterRegister(PyObject* self, PyObject* args) {
        PyObject* reg1 = nullptr;
        PyObject* reg2 = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &reg1, &reg2);

        if (reg1 == nullptr || !PyRegister_Check(reg1))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterRegister(): Expects a Register as first argument.");

        if (reg2 == nullptr || !PyRegister_Check(reg2))
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterRegister(): Expects a Register as second argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->taintUnionRegisterRegister(*PyRegister_AsRegister(reg1), *PyRegister_AsRegister(reg2)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_unmapMemory(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;
        triton::uint64 c_baseAddr = 0;
        triton::usize c_size      = 1;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &baseAddr, &size);

        if (baseAddr == nullptr || (!PyLong_Check(baseAddr) && !PyInt_Check(baseAddr)))
          return PyErr_Format(PyExc_TypeError, "unmapMemory(): Expects a base address (integer) as first argument.");

        if (size != nullptr && !PyLong_Check(size) && !PyInt_Check(size))
          return PyErr_Format(PyExc_TypeError, "unmapMemory(): Expects a size (integer) as second argument.");

        try {
          c_baseAddr = PyLong_AsUint64(baseAddr);
          if (size != nullptr)
            c_size = PyLong_AsUsize(size);
          PyTritonContext_AsTritonContext(self)->unmapMemory(c_baseAddr, c_size);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_unrollAst(PyObject* self, PyObject* node) {
        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "unrollAst(): Expects a AstNode as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->unrollAst(PyAstNode_AsAstNode(node)));
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
            return PyErr_Format(PyExc_TypeError, "untaintMemory(): Expects a MemoryAccess or an integer as argument.");
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_untaintRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "untaintRegister(): Expects a Register as argument.");

        try {
          if (PyTritonContext_AsTritonContext(self)->untaintRegister(*PyRegister_AsRegister(reg)) == true)
            Py_RETURN_TRUE;
          Py_RETURN_FALSE;
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getParentRegister(PyObject* self, PyObject* reg) {
        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getParentRegister(): Expects a Register as argument.");

        try {
          return PyRegister(PyTritonContext_AsTritonContext(self)->getParentRegister(PyRegister_AsRegister(reg)->getId()));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getattro(PyObject* self, PyObject* name) {
        try {
          /* Access to the registers attribute */
          if (std::string(PyString_AsString(name)) == "registers") {

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
        {"clearPathConstraints",                (PyCFunction)TritonContext_clearPathConstraints,                   METH_NOARGS,        ""},
        {"concretizeAllMemory",                 (PyCFunction)TritonContext_concretizeAllMemory,                    METH_NOARGS,        ""},
        {"concretizeAllRegister",               (PyCFunction)TritonContext_concretizeAllRegister,                  METH_NOARGS,        ""},
        {"concretizeMemory",                    (PyCFunction)TritonContext_concretizeMemory,                       METH_O,             ""},
        {"concretizeRegister",                  (PyCFunction)TritonContext_concretizeRegister,                     METH_O,             ""},
        {"convertExpressionToSymbolicVariable", (PyCFunction)TritonContext_convertExpressionToSymbolicVariable,    METH_VARARGS,       ""},
        {"convertMemoryToSymbolicVariable",     (PyCFunction)TritonContext_convertMemoryToSymbolicVariable,        METH_VARARGS,       ""},
        {"convertRegisterToSymbolicVariable",   (PyCFunction)TritonContext_convertRegisterToSymbolicVariable,      METH_VARARGS,       ""},
        {"createSymbolicFlagExpression",        (PyCFunction)TritonContext_createSymbolicFlagExpression,           METH_VARARGS,       ""},
        {"createSymbolicMemoryExpression",      (PyCFunction)TritonContext_createSymbolicMemoryExpression,         METH_VARARGS,       ""},
        {"createSymbolicRegisterExpression",    (PyCFunction)TritonContext_createSymbolicRegisterExpression,       METH_VARARGS,       ""},
        {"createSymbolicVolatileExpression",    (PyCFunction)TritonContext_createSymbolicVolatileExpression,       METH_VARARGS,       ""},
        {"disassembly",                         (PyCFunction)TritonContext_disassembly,                            METH_O,             ""},
        {"enableMode",                          (PyCFunction)TritonContext_enableMode,                             METH_VARARGS,       ""},
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
        {"getPathConstraints",                  (PyCFunction)TritonContext_getPathConstraints,                     METH_NOARGS,        ""},
        {"getPathConstraintsAst",               (PyCFunction)TritonContext_getPathConstraintsAst,                  METH_NOARGS,        ""},
        {"getRegister",                         (PyCFunction)TritonContext_getRegister,                            METH_O,             ""},
        {"getRegisterAst",                      (PyCFunction)TritonContext_getRegisterAst,                         METH_O,             ""},
        {"getSymbolicExpressionFromId",         (PyCFunction)TritonContext_getSymbolicExpressionFromId,            METH_O,             ""},
        {"getSymbolicExpressions",              (PyCFunction)TritonContext_getSymbolicExpressions,                 METH_NOARGS,        ""},
        {"getSymbolicMemory",                   (PyCFunction)TritonContext_getSymbolicMemory,                      METH_VARARGS,       ""},
        {"getSymbolicMemoryValue",              (PyCFunction)TritonContext_getSymbolicMemoryValue,                 METH_O,             ""},
        {"getSymbolicRegister",                 (PyCFunction)TritonContext_getSymbolicRegister,                    METH_O,             ""},
        {"getSymbolicRegisterValue",            (PyCFunction)TritonContext_getSymbolicRegisterValue,               METH_O,             ""},
        {"getSymbolicRegisters",                (PyCFunction)TritonContext_getSymbolicRegisters,                   METH_NOARGS,        ""},
        {"getSymbolicVariableFromId",           (PyCFunction)TritonContext_getSymbolicVariableFromId,              METH_O,             ""},
        {"getSymbolicVariableFromName",         (PyCFunction)TritonContext_getSymbolicVariableFromName,            METH_O,             ""},
        {"getSymbolicVariables",                (PyCFunction)TritonContext_getSymbolicVariables,                   METH_NOARGS,        ""},
        {"getTaintedMemory",                    (PyCFunction)TritonContext_getTaintedMemory,                       METH_NOARGS,        ""},
        {"getTaintedRegisters",                 (PyCFunction)TritonContext_getTaintedRegisters,                    METH_NOARGS,        ""},
        {"getTaintedSymbolicExpressions",       (PyCFunction)TritonContext_getTaintedSymbolicExpressions,          METH_NOARGS,        ""},
        {"isArchitectureValid",                 (PyCFunction)TritonContext_isArchitectureValid,                    METH_NOARGS,        ""},
        {"isFlag",                              (PyCFunction)TritonContext_isFlag,                                 METH_O,             ""},
        {"isMemoryMapped",                      (PyCFunction)TritonContext_isMemoryMapped,                         METH_VARARGS,       ""},
        {"isMemorySymbolized",                  (PyCFunction)TritonContext_isMemorySymbolized,                     METH_O,             ""},
        {"isMemoryTainted",                     (PyCFunction)TritonContext_isMemoryTainted,                        METH_O,             ""},
        {"isModeEnabled",                       (PyCFunction)TritonContext_isModeEnabled,                          METH_O,             ""},
        {"isRegister",                          (PyCFunction)TritonContext_isRegister,                             METH_O,             ""},
        {"isRegisterSymbolized",                (PyCFunction)TritonContext_isRegisterSymbolized,                   METH_O,             ""},
        {"isRegisterTainted",                   (PyCFunction)TritonContext_isRegisterTainted,                      METH_O,             ""},
        {"isRegisterValid",                     (PyCFunction)TritonContext_isRegisterValid,                        METH_O,             ""},
        {"isSat",                               (PyCFunction)TritonContext_isSat,                                  METH_O     ,        ""},
        {"isSymbolicEngineEnabled",             (PyCFunction)TritonContext_isSymbolicEngineEnabled,                METH_NOARGS,        ""},
        {"isSymbolicExpressionIdExists",        (PyCFunction)TritonContext_isSymbolicExpressionIdExists,           METH_O,             ""},
        {"isTaintEngineEnabled",                (PyCFunction)TritonContext_isTaintEngineEnabled,                   METH_NOARGS,        ""},
        {"newSymbolicExpression",               (PyCFunction)TritonContext_newSymbolicExpression,                  METH_VARARGS,       ""},
        {"newSymbolicVariable",                 (PyCFunction)TritonContext_newSymbolicVariable,                    METH_VARARGS,       ""},
        {"processing",                          (PyCFunction)TritonContext_processing,                             METH_O,             ""},
        {"removeAllCallbacks",                  (PyCFunction)TritonContext_removeAllCallbacks,                     METH_NOARGS,        ""},
        {"removeCallback",                      (PyCFunction)TritonContext_removeCallback,                         METH_VARARGS,       ""},
        {"reset",                               (PyCFunction)TritonContext_reset,                                  METH_NOARGS,        ""},
        {"setArchitecture",                     (PyCFunction)TritonContext_setArchitecture,                        METH_O,             ""},
        {"setAstRepresentationMode",            (PyCFunction)TritonContext_setAstRepresentationMode,               METH_O,             ""},
        {"setConcreteMemoryAreaValue",          (PyCFunction)TritonContext_setConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"setConcreteMemoryValue",              (PyCFunction)TritonContext_setConcreteMemoryValue,                 METH_VARARGS,       ""},
        {"setConcreteRegisterValue",            (PyCFunction)TritonContext_setConcreteRegisterValue,               METH_VARARGS,       ""},
        {"setConcreteVariableValue",            (PyCFunction)TritonContext_setConcreteVariableValue,               METH_VARARGS,       ""},
        {"setTaintMemory",                      (PyCFunction)TritonContext_setTaintMemory,                         METH_VARARGS,       ""},
        {"setTaintRegister",                    (PyCFunction)TritonContext_setTaintRegister,                       METH_VARARGS,       ""},
        {"simplify",                            (PyCFunction)TritonContext_simplify,                               METH_VARARGS,       ""},
        {"sliceExpressions",                    (PyCFunction)TritonContext_sliceExpressions,                       METH_O,             ""},
        {"taintAssignmentMemoryImmediate",      (PyCFunction)TritonContext_taintAssignmentMemoryImmediate,         METH_O,             ""},
        {"taintAssignmentMemoryMemory",         (PyCFunction)TritonContext_taintAssignmentMemoryMemory,            METH_VARARGS,       ""},
        {"taintAssignmentMemoryRegister",       (PyCFunction)TritonContext_taintAssignmentMemoryRegister,          METH_VARARGS,       ""},
        {"taintAssignmentRegisterImmediate",    (PyCFunction)TritonContext_taintAssignmentRegisterImmediate,       METH_O,             ""},
        {"taintAssignmentRegisterMemory",       (PyCFunction)TritonContext_taintAssignmentRegisterMemory,          METH_VARARGS,       ""},
        {"taintAssignmentRegisterRegister",     (PyCFunction)TritonContext_taintAssignmentRegisterRegister,        METH_VARARGS,       ""},
        {"taintMemory",                         (PyCFunction)TritonContext_taintMemory,                            METH_O,             ""},
        {"taintRegister",                       (PyCFunction)TritonContext_taintRegister,                          METH_O,             ""},
        {"taintUnionMemoryImmediate",           (PyCFunction)TritonContext_taintUnionMemoryImmediate,              METH_O,             ""},
        {"taintUnionMemoryMemory",              (PyCFunction)TritonContext_taintUnionMemoryMemory,                 METH_VARARGS,       ""},
        {"taintUnionMemoryRegister",            (PyCFunction)TritonContext_taintUnionMemoryRegister,               METH_VARARGS,       ""},
        {"taintUnionRegisterImmediate",         (PyCFunction)TritonContext_taintUnionRegisterImmediate,            METH_O,             ""},
        {"taintUnionRegisterMemory",            (PyCFunction)TritonContext_taintUnionRegisterMemory,               METH_VARARGS,       ""},
        {"taintUnionRegisterRegister",          (PyCFunction)TritonContext_taintUnionRegisterRegister,             METH_VARARGS,       ""},
        {"unmapMemory",                         (PyCFunction)TritonContext_unmapMemory,                            METH_VARARGS,       ""},
        {"unrollAst",                           (PyCFunction)TritonContext_unrollAst,                              METH_O,             ""},
        {"untaintMemory",                       (PyCFunction)TritonContext_untaintMemory,                          METH_O,             ""},
        {"untaintRegister",                     (PyCFunction)TritonContext_untaintRegister,                        METH_O,             ""},
        {nullptr,                               nullptr,                                                           0,                  nullptr}
      };


      //! Description of the python representation of a TritonContext
      PyTypeObject TritonContext_Type = {
#ifdef IS_PY3
        PyVarObject_HEAD_INIT(&PyType_Type, 0)
#else
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
#endif
        "TritonContext",                            /* tp_name */
        sizeof(TritonContext_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        (destructor)TritonContext_dealloc,          /* tp_dealloc */
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
        (destructor)TritonContext_dealloc,          /* tp_del */
#ifdef IS_PY3
        0,                                          /* tp_version_tag */
        (destructor)TritonContext_dealloc,          /* tp_dealloc */
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
