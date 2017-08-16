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

\section tritonContext_py_api Python API - Classes and methods of the TritonContext class
<hr>

\subsection TritonContext_py_api_classes Classes

- \ref py_AstNode_page
- \ref py_AstContext_page
- \ref py_BitsVector_page
- \ref py_PathConstraint_page
- \ref py_Register_page
- \ref py_SolverModel_page
- \ref py_SymbolicExpression_page
- \ref py_SymbolicVariable_page

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

- <b>\ref py_AstNode_page buildSymbolicImmediate(\ref py_Immediate_page imm)</b><br>
Builds a symbolic immediate from a \ref py_Immediate_page.

- <b>\ref py_AstNode_page buildSymbolicMemory(\ref py_MemoryAccess_page mem)</b><br>
Builds a symbolic memory cell from a \ref py_MemoryAccess_page with the SSA form.

- <b>\ref py_AstNode_page buildSymbolicRegister(\ref py_Register_page reg)</b><br>
Builds a symbolic register from a \ref py_Register_page with the SSA form.

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

- <b>integer getConcreteRegisterValue(\ref py_Register_page reg)</b><br>
Returns the concrete value of a register.

- <b>integer getConcreteSymbolicVariableValue(\ref py_SymbolicVariable_page symVar)</b><br>
Returns the concrete value of a symbolic variable.

- <b>\ref py_AstNode_page getFullAst(\ref py_AstNode_page node)</b><br>
Returns the full AST without SSA form from a given root node.

- <b>\ref py_AstNode_page getFullAstFromId(integer symExprId)</b><br>
Returns the full AST without SSA form from a symbolic expression id.

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

- <b>integer getSymbolicRegisterId(\ref py_Register_page reg)</b><br>
Returns the symbolic expression id corresponding to a register.

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

- <b>void setConcreteMemoryValue(\ref py_MemoryAccess_page mem, integer value)</b><br>
Sets the concrete value of memory cells. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteRegisterValue(\ref py_Register_page reg, integer value)</b><br>
Sets the concrete value of a register. Note that by setting a concrete value will probably imply a desynchronization with
the symbolic state (if it exists). You should probably use the concretize functions after this.

- <b>void setConcreteSymbolicVariableValue(\ref py_SymbolicVariable_page symVar, integer value)</b><br>
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

      static void TritonContext_dealloc(PyObject* self) {
        delete PyTritonContext_AsTritonContext(self);
        Py_XDECREF(((TritonContext_Object*)self)->regAttr);
        Py_DECREF(self);
      }


      static void TritonContext_fillRegistersAttribute(PyObject* self) {
        /* Fill self->regAttr */
        auto& regs = PyTritonContext_AsTritonContext(self)->getAllRegisters();

        PyObject* registersDict = xPyDict_New();
        for (auto& reg : regs)
          PyDict_SetItem(registersDict, PyString_FromString(reg.second.getName().c_str()), PyRegister(reg.second));

        Py_XDECREF(((TritonContext_Object*)(self))->regAttr);
        ((TritonContext_Object*)(self))->regAttr = xPyClass_New(nullptr, registersDict, xPyString_FromString("registers"));
      }


      static PyObject* TritonContext_addCallback(PyObject* self, PyObject* args) {
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &function, &mode);

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "addCallback(): Architecture is not defined.");

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "addCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "addCallback(): Expects a CALLBACK as second argument.");

        try {
          switch (static_cast<triton::callbacks::callback_e>(PyLong_AsUint32(mode))) {
            // FIXME : We should incref the function object as it could be a lambda or a temporary function

            case callbacks::GET_CONCRETE_MEMORY_VALUE:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::getConcreteMemoryValueCallback([function](triton::API& api, const triton::arch::MemoryAccess& mem) {
                /********* Lambda *********/
                /* Create function args */
                PyObject* args = triton::bindings::python::xPyTuple_New(2);
                PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                PyTuple_SetItem(args, 1, triton::bindings::python::PyMemoryAccess(mem));

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
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::getConcreteRegisterValueCallback([function](triton::API& api, const triton::arch::Register& reg){
                /********* Lambda *********/
                  /* Create function args */
                  PyObject* args = triton::bindings::python::xPyTuple_New(2);
                  PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                  PyTuple_SetItem(args, 1, triton::bindings::python::PyRegister(reg));

                  /* Call the callback */
                  PyObject* ret = PyObject_CallObject(function, args);

                  /* Check the call */
                  if (ret == nullptr) {
                    PyErr_Print();
                    throw triton::exceptions::Callbacks("Callbacks::processCallbacks(GET_CONCRETE_REGISTER_VALUE): Fail to call the python callback.");
                  }

                  Py_DECREF(args);
                /********* End of lambda *********/
                }, function));
              break;

            case callbacks::SYMBOLIC_SIMPLIFICATION:
              PyTritonContext_AsTritonContext(self)->addCallback(callbacks::symbolicSimplificationCallback([function](triton::API& api, triton::ast::AbstractNode* node) {
                /********* Lambda *********/
                PyObject* args = triton::bindings::python::xPyTuple_New(2);
                PyTuple_SetItem(args, 0, triton::bindings::python::PyTritonContextRef(api));
                PyTuple_SetItem(args, 1, triton::bindings::python::PyAstNode(node));

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


      static PyObject* TritonContext_assignSymbolicExpressionToMemory(PyObject* self, PyObject* args) {
        PyObject* se  = nullptr;
        PyObject* mem = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &se, &mem);

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Architecture is not defined.");

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Expects a SymbolicExpression as first argument.");

        if (mem == nullptr || (!PyMemoryAccess_Check(mem)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToMemory(): Expects a MemoryAccess as second argument.");

        triton::engines::symbolic::SymbolicExpression* arg1 = PySymbolicExpression_AsSymbolicExpression(se);
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Architecture is not defined.");

        if (se == nullptr || (!PySymbolicExpression_Check(se)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a SymbolicExpression as first argument.");

        if (reg == nullptr || (!PyRegister_Check(reg)))
          return PyErr_Format(PyExc_TypeError, "assignSymbolicExpressionToRegister(): Expects a Register as second argument.");

        triton::engines::symbolic::SymbolicExpression* arg1 = PySymbolicExpression_AsSymbolicExpression(se);
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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSemantics(): Architecture is not defined.");

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


      static PyObject* TritonContext_buildSymbolicImmediate(PyObject* self, PyObject* imm) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSymbolicImmediate(): Architecture is not defined.");

        if (!PyImmediate_Check(imm))
          return PyErr_Format(PyExc_TypeError, "buildSymbolicImmediate(): Expects an Immediate as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->buildSymbolicImmediate(*PyImmediate_AsImmediate(imm)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_buildSymbolicMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSymbolicMemory(): Architecture is not defined.");

        if (!PyMemoryAccess_Check(mem))
          return PyErr_Format(PyExc_TypeError, "buildSymbolicMemory(): Expects an MemoryAccess as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->buildSymbolicMemory(*PyMemoryAccess_AsMemoryAccess(mem)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_buildSymbolicRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "buildSymbolicRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "buildSymbolicRegister(): Expects an Register as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->buildSymbolicRegister(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_clearPathConstraints(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "clearPathConstraints(): Architecture is not defined.");
        PyTritonContext_AsTritonContext(self)->clearPathConstraints();

        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeAllMemory(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeAllMemory(): Architecture is not defined.");
        PyTritonContext_AsTritonContext(self)->concretizeAllMemory();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeAllRegister(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeAllRegister(): Architecture is not defined.");
        PyTritonContext_AsTritonContext(self)->concretizeAllRegister();
        Py_INCREF(Py_None);
        return Py_None;
      }


      static PyObject* TritonContext_concretizeMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeMemory(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "concretizeRegister(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertMemoryToSymbolicVariable(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "convertRegisterToSymbolicVariable(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicFlagExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
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
        triton::ast::AbstractNode *arg2 = PyAstNode_AsAstNode(node);
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicMemoryExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicRegisterExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
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
        triton::ast::AbstractNode *arg2 = PyAstNode_AsAstNode(node);
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "createSymbolicVolatileExpression(): Architecture is not defined.");

        if (inst == nullptr || (!PyInstance_Check(inst)))
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
          return PySymbolicExpression(PyTritonContext_AsTritonContext(self)->createSymbolicVolatileExpression(arg1, arg2, ccomment));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_disassembly(PyObject* self, PyObject* inst) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "disassembly(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableMode(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableSymbolicEngine(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "enableTaintEngine(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "evaluateAstViaZ3(): Architecture is not defined.");

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "evaluateAstViaZ3(): Expects a AstNode as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->evaluateAstViaZ3(PyAstNode_AsAstNode(node)));
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


      static PyObject* TritonContext_getAllRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAllRegisters(): Architecture is not defined.");

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
        return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getArchitecture());
      }


      static PyObject* TritonContext_getAstContext(PyObject* self, PyObject* noarg) {
        try {
          return PyAstContext(PyTritonContext_AsTritonContext(self)->getAstContext());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getAstDictionariesStats(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstDictionariesStats(): Architecture is not defined.");

        try {
          std::map<std::string, triton::usize> stats = PyTritonContext_AsTritonContext(self)->getAstDictionariesStats();

          ret = xPyDict_New();
          for (auto it = stats.begin(); it != stats.end(); it++)
            PyDict_SetItem(ret, PyString_FromString(it->first.c_str()), PyLong_FromUsize(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getAstFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getAstFromId(): Expects an integer as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getAstFromId(PyLong_AsUsize(symExprId)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getAstRepresentationMode(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getAstRepresentationMode(): Architecture is not defined.");

        return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getAstRepresentationMode());
      }


      static PyObject* TritonContext_getConcreteMemoryAreaValue(PyObject* self, PyObject* args) {
        triton::uint8*  area = nullptr;
        PyObject*       ret  = nullptr;
        PyObject*       addr = nullptr;
        PyObject*       size = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &addr, &size);

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteMemoryAreaValue(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteMemoryValue(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteRegisterValue(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getConcreteRegisterValue(): Expects a Register as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteRegisterValue(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getConcreteSymbolicVariableValue(PyObject* self, PyObject* symVar) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getConcreteSymbolicVariableValue(): Architecture is not defined.");

        if (!PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "getConcreteSymbolicVariableValue(): Expects a SymbolicVariable as argument.");

        try {
          return PyLong_FromUint512(PyTritonContext_AsTritonContext(self)->getConcreteSymbolicVariableValue(*PySymbolicVariable_AsSymbolicVariable(symVar)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getFullAst(PyObject* self, PyObject* node) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getFullAst(): Architecture is not defined.");

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getFullAst(): Expects a AstNode as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getFullAst(PyAstNode_AsAstNode(node)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getFullAstFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getFullAstFromId(): Architecture is not defined.");

        if (!PyLong_Check(symExprId) && !PyInt_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "getFullAstFromId(): Expects an integer as argument.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getFullAstFromId(PyLong_AsUsize(symExprId)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getModel(PyObject* self, PyObject* node) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getModel(): Architecture is not defined.");

        if (!PyAstNode_Check(node))
          return PyErr_Format(PyExc_TypeError, "getModel(): Expects a AstNode as argument.");

        try {
          ret = xPyDict_New();
          auto model = PyTritonContext_AsTritonContext(self)->getModel(PyAstNode_AsAstNode(node));
          for (auto it = model.begin(); it != model.end(); it++) {
            PyDict_SetItem(ret, PyLong_FromUint32(it->first), PySolverModel(it->second));
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getModels(): Architecture is not defined.");

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


      static PyObject* TritonContext_getParentRegisters(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getParentRegisters(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getPathConstraintsAst(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getPathConstraintsAst(): Architecture is not defined.");

        try {
          return PyAstNode(PyTritonContext_AsTritonContext(self)->getPathConstraintsAst());
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getRegister(PyObject* self, PyObject* regIn) {
        triton::arch::registers_e rid = triton::arch::ID_REG_INVALID;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getRegister(): Architecture is not defined.");

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


      static PyObject* TritonContext_getRegisterBitSize(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getRegisterBitSize());
      }


      static PyObject* TritonContext_getRegisterSize(PyObject* self, PyObject* noarg) {
        return PyLong_FromUint32(PyTritonContext_AsTritonContext(self)->getRegisterSize());
      }


      static PyObject* TritonContext_getSymbolicExpressionFromId(PyObject* self, PyObject* symExprId) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicExpressionFromId(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicExpressions(): Architecture is not defined.");

        try {
          const auto& expressions = PyTritonContext_AsTritonContext(self)->getSymbolicExpressions();

          ret = xPyDict_New();
          for (auto it = expressions.begin(); it != expressions.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getSymbolicMemory(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemory(): Architecture is not defined.");

        try {
          auto regs = PyTritonContext_AsTritonContext(self)->getSymbolicMemory();

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


      static PyObject* TritonContext_getSymbolicMemoryId(PyObject* self, PyObject* addr) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryId(): Architecture is not defined.");

        if (!PyLong_Check(addr) && !PyInt_Check(addr))
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryId(): Expects an integer as argument.");

        try {
          return PyLong_FromUsize(PyTritonContext_AsTritonContext(self)->getSymbolicMemoryId(PyLong_AsUint64(addr)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicMemoryValue(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicMemoryValue(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisters(): Architecture is not defined.");

        try {
          auto regs = PyTritonContext_AsTritonContext(self)->getSymbolicRegisters();

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


      static PyObject* TritonContext_getSymbolicRegisterId(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterId(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterId(): Expects a Register as argument.");

        try {
          return PyLong_FromUsize(PyTritonContext_AsTritonContext(self)->getSymbolicRegisterId(*PyRegister_AsRegister(reg)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* TritonContext_getSymbolicRegisterValue(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicRegisterValue(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromId(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getSymbolicVariableFromName(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicVariables(): Architecture is not defined.");

        try {
          const auto& variables = PyTritonContext_AsTritonContext(self)->getSymbolicVariables();

          ret = xPyDict_New();
          for (auto sv: variables)
            PyDict_SetItem(ret, PyLong_FromUsize(sv.first), PySymbolicVariable(sv.second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_getTaintedMemory(PyObject* self, PyObject* noarg) {
        PyObject* ret = nullptr;
        triton::usize size = 0, index = 0;

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedMemory(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedRegisters(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getTaintedSymbolicExpressions(): Architecture is not defined.");

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
        if (PyTritonContext_AsTritonContext(self)->isArchitectureValid() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isFlag(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isFlag(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isFlag(): Expects a Register as argument.");

        if (PyTritonContext_AsTritonContext(self)->isFlag(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isMemoryMapped(PyObject* self, PyObject* args) {
        PyObject* baseAddr        = nullptr;
        PyObject* size            = nullptr;
        triton::uint64 c_baseAddr = 0;
        triton::usize c_size      = 1;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &baseAddr, &size);

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemoryMapped(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemorySymbolized(): Architecture is not defined.");

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

        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isMemoryTainted(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isMemoryTainted(): Architecture is not defined.");

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

        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isRegister(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegister(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegister(): Expects a Register as argument.");

        if (PyTritonContext_AsTritonContext(self)->isRegister(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isRegisterSymbolized(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegisterSymbolized(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterSymbolized(): Expects a Register as argument.");

        if (PyTritonContext_AsTritonContext(self)->isRegisterSymbolized(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isRegisterTainted(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegisterTainted(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterTainted(): Expects a Register as argument.");

        if (PyTritonContext_AsTritonContext(self)->isRegisterTainted(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isRegisterValid(PyObject* self, PyObject* reg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isRegisterValid(): Architecture is not defined.");

        if (!PyRegister_Check(reg))
          return PyErr_Format(PyExc_TypeError, "isRegisterValid(): Expects a Register as argument.");

        if (PyTritonContext_AsTritonContext(self)->isRegisterValid(*PyRegister_AsRegister(reg)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isSymbolicEngineEnabled(PyObject* self, PyObject* noarg) {
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isSymbolicEngineEnabled(): Architecture is not defined.");

        if (PyTritonContext_AsTritonContext(self)->isSymbolicEngineEnabled() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isSymbolicExpressionIdExists(PyObject* self, PyObject* symExprId) {
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Architecture is not defined.");

        if (!PyInt_Check(symExprId) && !PyLong_Check(symExprId))
          return PyErr_Format(PyExc_TypeError, "isSymbolicExpressionIdExists(): Expects an integer as argument.");

        if (PyTritonContext_AsTritonContext(self)->isSymbolicExpressionIdExists(PyLong_AsUsize(symExprId)) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isModeEnabled(PyObject* self, PyObject* mode) {
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isModeEnabled(): Architecture is not defined.");

        if (!PyInt_Check(mode) && !PyLong_Check(mode))
          return PyErr_Format(PyExc_TypeError, "isModeEnabled(): Expects a MODE as argument.");

        if (PyTritonContext_AsTritonContext(self)->isModeEnabled(static_cast<enum triton::modes::mode_e>(PyLong_AsUint32(mode))) == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_isTaintEngineEnabled(PyObject* self, PyObject* noarg) {
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "isTaintEngineEnabled(): Architecture is not defined.");

        if (PyTritonContext_AsTritonContext(self)->isTaintEngineEnabled() == true)
          Py_RETURN_TRUE;
        Py_RETURN_FALSE;
      }


      static PyObject* TritonContext_newSymbolicExpression(PyObject* self, PyObject* args) {
        PyObject* node          = nullptr;
        PyObject* comment       = nullptr;
        std::string ccomment    = "";

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &node, &comment);

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "newSymbolicExpression(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "newSymbolicVariable(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "processing(): Architecture is not defined.");

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
        PyObject* function = nullptr;
        PyObject* mode     = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &function, &mode);

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Architecture is not defined.");

        if (function == nullptr || !PyCallable_Check(function))
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Expects a function as first argument.");

        if (mode == nullptr || (!PyLong_Check(mode) && !PyInt_Check(mode)))
          return PyErr_Format(PyExc_TypeError, "removeCallback(): Expects a CALLBACK as second argument.");

        try {
          switch (static_cast<triton::callbacks::callback_e>(PyLong_AsUint32(mode))) {
            case callbacks::GET_CONCRETE_MEMORY_VALUE:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::getConcreteMemoryValueCallback(nullptr, function));
              break;
            case callbacks::GET_CONCRETE_REGISTER_VALUE:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::getConcreteRegisterValueCallback(nullptr, function));
              break;
            case callbacks::SYMBOLIC_SIMPLIFICATION:
              PyTritonContext_AsTritonContext(self)->removeCallback(callbacks::symbolicSimplificationCallback(nullptr, function));
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


      static PyObject* TritonContext_resetEngines(PyObject* self, PyObject* noarg) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "resetEngines(): Architecture is not defined.");

        try {
          PyTritonContext_AsTritonContext(self)->resetEngines();
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
          PyTritonContext_AsTritonContext(self)->setArchitecture(PyLong_AsUint32(arg));
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setConcreteRegisterValue(): Architecture is not defined.");

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


      static PyObject* TritonContext_setConcreteSymbolicVariableValue(PyObject* self, PyObject* args) {
        PyObject* symVar = nullptr;
        PyObject* value  = nullptr;

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &symVar, &value);

        if (symVar == nullptr || !PySymbolicVariable_Check(symVar))
          return PyErr_Format(PyExc_TypeError, "setConcreteSymbolicVariableValue(): Bad argument type.");

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setConcreteSymbolicVariableValue(): Architecture is not defined.");

        if (value == nullptr)
          return PyErr_Format(PyExc_TypeError, "setConcreteSymbolicVariableValue(): Expects a second argument as integer value.");

        try {
          PyTritonContext_AsTritonContext(self)->setConcreteSymbolicVariableValue(*PySymbolicVariable_AsSymbolicVariable(symVar), PyLong_AsUint512(value));
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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setTaintMemory(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "setTaintRegister(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "simplify(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "sliceExpressions(): Architecture is not defined.");

        if (!PySymbolicExpression_Check(expr))
          return PyErr_Format(PyExc_TypeError, "sliceExpressions(): Expects a SymbolicExpression as argument.");

        try {
          auto exprs = PyTritonContext_AsTritonContext(self)->sliceExpressions(PySymbolicExpression_AsSymbolicExpression(expr));

          ret = xPyDict_New();
          for (auto it = exprs.begin(); it != exprs.end(); it++)
            PyDict_SetItem(ret, PyLong_FromUsize(it->first), PySymbolicExpression(it->second));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

        return ret;
      }


      static PyObject* TritonContext_taintAssignmentMemoryImmediate(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryImmediate(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryMemory(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentMemoryRegister(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterImmediate(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterMemory(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintAssignmentRegisterRegister(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintMemory(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintRegister(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryImmediate(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryMemory(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionMemoryRegister(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterImmediate(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterMemory(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "taintUnionRegisterRegister(): Architecture is not defined.");

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

        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "unmapMemory(): Architecture is not defined.");

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


      static PyObject* TritonContext_untaintMemory(PyObject* self, PyObject* mem) {
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintMemory(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "untaintRegister(): Architecture is not defined.");

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
        /* Check if the architecture is definied */
        if (PyTritonContext_AsTritonContext(self)->getArchitecture() == triton::arch::ARCH_INVALID)
          return PyErr_Format(PyExc_TypeError, "getParentRegister(): Architecture is not defined.");

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
        {"buildSymbolicImmediate",              (PyCFunction)TritonContext_buildSymbolicImmediate,                 METH_O,             ""},
        {"buildSymbolicMemory",                 (PyCFunction)TritonContext_buildSymbolicMemory,                    METH_O,             ""},
        {"buildSymbolicRegister",               (PyCFunction)TritonContext_buildSymbolicRegister,                  METH_O,             ""},
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
        {"getAstDictionariesStats",             (PyCFunction)TritonContext_getAstDictionariesStats,                METH_NOARGS,        ""},
        {"getAstFromId",                        (PyCFunction)TritonContext_getAstFromId,                           METH_O,             ""},
        {"getAstRepresentationMode",            (PyCFunction)TritonContext_getAstRepresentationMode,               METH_NOARGS,        ""},
        {"getConcreteMemoryAreaValue",          (PyCFunction)TritonContext_getConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"getConcreteMemoryValue",              (PyCFunction)TritonContext_getConcreteMemoryValue,                 METH_O,             ""},
        {"getConcreteRegisterValue",            (PyCFunction)TritonContext_getConcreteRegisterValue,               METH_O,             ""},
        {"getConcreteSymbolicVariableValue",    (PyCFunction)TritonContext_getConcreteSymbolicVariableValue,       METH_O,             ""},
        {"getFullAst",                          (PyCFunction)TritonContext_getFullAst,                             METH_O,             ""},
        {"getFullAstFromId",                    (PyCFunction)TritonContext_getFullAstFromId,                       METH_O,             ""},
        {"getModel",                            (PyCFunction)TritonContext_getModel,                               METH_O,             ""},
        {"getModels",                           (PyCFunction)TritonContext_getModels,                              METH_VARARGS,       ""},
        {"getParentRegister",                   (PyCFunction)TritonContext_getParentRegister,                      METH_O,             ""},
        {"getParentRegisters",                  (PyCFunction)TritonContext_getParentRegisters,                     METH_NOARGS,        ""},
        {"getPathConstraints",                  (PyCFunction)TritonContext_getPathConstraints,                     METH_NOARGS,        ""},
        {"getPathConstraintsAst",               (PyCFunction)TritonContext_getPathConstraintsAst,                  METH_NOARGS,        ""},
        {"getRegister",                         (PyCFunction)TritonContext_getRegister,                            METH_O,             ""},
        {"getRegisterBitSize",                  (PyCFunction)TritonContext_getRegisterBitSize,                     METH_NOARGS,        ""},
        {"getRegisterSize",                     (PyCFunction)TritonContext_getRegisterSize,                        METH_NOARGS,        ""},
        {"getSymbolicExpressionFromId",         (PyCFunction)TritonContext_getSymbolicExpressionFromId,            METH_O,             ""},
        {"getSymbolicExpressions",              (PyCFunction)TritonContext_getSymbolicExpressions,                 METH_NOARGS,        ""},
        {"getSymbolicMemory",                   (PyCFunction)TritonContext_getSymbolicMemory,                      METH_NOARGS,        ""},
        {"getSymbolicMemoryId",                 (PyCFunction)TritonContext_getSymbolicMemoryId,                    METH_O,             ""},
        {"getSymbolicMemoryValue",              (PyCFunction)TritonContext_getSymbolicMemoryValue,                 METH_O,             ""},
        {"getSymbolicRegisterId",               (PyCFunction)TritonContext_getSymbolicRegisterId,                  METH_O,             ""},
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
        {"isSymbolicEngineEnabled",             (PyCFunction)TritonContext_isSymbolicEngineEnabled,                METH_NOARGS,        ""},
        {"isSymbolicExpressionIdExists",        (PyCFunction)TritonContext_isSymbolicExpressionIdExists,           METH_O,             ""},
        {"isTaintEngineEnabled",                (PyCFunction)TritonContext_isTaintEngineEnabled,                   METH_NOARGS,        ""},
        {"newSymbolicExpression",               (PyCFunction)TritonContext_newSymbolicExpression,                  METH_VARARGS,       ""},
        {"newSymbolicVariable",                 (PyCFunction)TritonContext_newSymbolicVariable,                    METH_VARARGS,       ""},
        {"processing",                          (PyCFunction)TritonContext_processing,                             METH_O,             ""},
        {"removeAllCallbacks",                  (PyCFunction)TritonContext_removeAllCallbacks,                     METH_NOARGS,        ""},
        {"removeCallback",                      (PyCFunction)TritonContext_removeCallback,                         METH_VARARGS,       ""},
        {"resetEngines",                        (PyCFunction)TritonContext_resetEngines,                           METH_NOARGS,        ""},
        {"setArchitecture",                     (PyCFunction)TritonContext_setArchitecture,                        METH_O,             ""},
        {"setAstRepresentationMode",            (PyCFunction)TritonContext_setAstRepresentationMode,               METH_O,             ""},
        {"setConcreteMemoryAreaValue",          (PyCFunction)TritonContext_setConcreteMemoryAreaValue,             METH_VARARGS,       ""},
        {"setConcreteMemoryValue",              (PyCFunction)TritonContext_setConcreteMemoryValue,                 METH_VARARGS,       ""},
        {"setConcreteRegisterValue",            (PyCFunction)TritonContext_setConcreteRegisterValue,               METH_VARARGS,       ""},
        {"setConcreteSymbolicVariableValue",    (PyCFunction)TritonContext_setConcreteSymbolicVariableValue,       METH_VARARGS,       ""},
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
        {"untaintMemory",                       (PyCFunction)TritonContext_untaintMemory,                          METH_O,             ""},
        {"untaintRegister",                     (PyCFunction)TritonContext_untaintRegister,                        METH_O,             ""},
        {nullptr,                               nullptr,                                                           0,                  nullptr}
      };


      //! Description of the python representation of a TritonContext
      PyTypeObject TritonContext_Type = {
        PyObject_HEAD_INIT(&PyType_Type)
        0,                                          /* ob_size */
        "TritonContext",                            /* tp_name */
        sizeof(TritonContext_Object),               /* tp_basicsize */
        0,                                          /* tp_itemsize */
        TritonContext_dealloc,                      /* tp_dealloc */
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
        0,                                          /* tp_del */
        0                                           /* tp_version_tag */
      };


      PyObject* PyTritonContext(void) {
        PyType_Ready(&TritonContext_Type);
        TritonContext_Object* object = PyObject_NEW(TritonContext_Object, &TritonContext_Type);

        if (object != nullptr) {
          object->api = new triton::API();
          object->regAttr = nullptr;
        }

        return (PyObject*)object;
      }


      PyObject* PyTritonContextRef(triton::API& api) {
        PyType_Ready(&TritonContext_Type);
        TritonContext_Object* object = PyObject_NEW(TritonContext_Object, &TritonContext_Type);

        if (object != nullptr) {
          object->api = &api;
          object->regAttr = nullptr;
        }

        Py_INCREF(object); // We don't have ownership of the API so don't call the dealloc
        // FIXME: we should define a context without dealloc for this
        return (PyObject*)object;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
