//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/basicBlock.hpp>
#include <triton/bitsVector.hpp>
#include <triton/exceptions.hpp>
#include <triton/immediate.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>



/*! \page py_triton_page Python bindings of libTriton
    \brief [**python api**] All information about libTriton's Python API.
    \anchor triton

\section triton_py_api Python API - Methods and namespaces of the triton module
<hr>

This project works using a `TritonContext` which contains all the required internal state
to simulate your instructions. You may also find [helpers](https://github.com/JonathanSalwan/Triton/tree/master/src/examples/python)
to wrap more generic concepts.

\subsection triton_py_api_classes Classes

- \ref py_AstContext_page
- \ref py_AstNode_page
- \ref py_BasicBlock_page
- \ref py_BitsVector_page
- \ref py_Immediate_page
- \ref py_Instruction_page
- \ref py_MemoryAccess_page
- \ref py_PathConstraint_page
- \ref py_Register_page
- \ref py_SolverModel_page
- \ref py_SymbolicExpression_page
- \ref py_SymbolicVariable_page
- \ref py_TritonContext_page


\subsection triton_py_api_namespaces Namespaces

- \ref py_ARCH_page
- \ref py_AST_NODE_page
- \ref py_AST_REPRESENTATION_page
- \ref py_CALLBACK_page
- \ref py_CONDITION_page
- \ref py_CPUSIZE_page
- \ref py_EXCEPTION_page
- \ref py_EXTEND_page
- \ref py_MODE_page
- \ref py_OPCODE_page
- \ref py_OPERAND_page
- \ref py_PREFIX_page
- \ref py_REG_page
- \ref py_SHIFT_page
- \ref py_SOLVER_STATE_page
- \ref py_SOLVER_page
- \ref py_STUBS_page
- \ref py_SYMBOLIC_page
- \ref py_VERSION_page

*/



namespace triton {
  namespace bindings {
    namespace python {

      static PyObject* triton_BasicBlock(PyObject* self, PyObject* args) {
        PyObject* obj = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|O", &obj) == false) {
          return PyErr_Format(PyExc_TypeError, "BasicBlock(): Invalid constructor.");
        }

        try {
          /* Check if it's a default constructor */
          if (obj == nullptr)
            return PyBasicBlock();

          /* Check if argument is a list of instruction */
          else if (obj != nullptr && PyList_Check(obj)) {
            triton::arch::BasicBlock block;

            for (Py_ssize_t i = 0; i < PyList_Size(obj); i++) {
              PyObject* item = PyList_GetItem(obj, i);

              if (PyInstruction_Check(item) == false)
                return PyErr_Format(PyExc_TypeError, "BasicBlock(): All items must be an Instruction objet.");

              block.add(*PyInstruction_AsInstruction(item));
            }

            return PyBasicBlock(block);
          }

          /* Otherwise, invalid constructor */
          else {
            return PyErr_Format(PyExc_TypeError, "BasicBlock(): Invalid constructor.");
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }

      static PyObject* triton_Immediate(PyObject* self, PyObject* args) {
        PyObject* value = nullptr;
        PyObject* size  = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &value, &size) == false) {
          return PyErr_Format(PyExc_TypeError, "Immediate(): Invalid constructor.");
        }

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
        PyObject* arg1 = nullptr;
        PyObject* arg2 = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &arg1, &arg2) == false) {
          return PyErr_Format(PyExc_TypeError, "Instruction(): Invalid constructor.");
        }

        try {
          /* Instruction() */
          if (arg1 == nullptr)
            return PyInstruction();

          /* Instruction(opcode) */
          else if (arg1 && PyBytes_Check(arg1) && arg2 == nullptr) {
            triton::uint8* opc  = reinterpret_cast<triton::uint8*>(PyBytes_AsString(arg1));
            triton::uint32 size = static_cast<triton::uint32>(PyBytes_Size(arg1));
            return PyInstruction(opc, size);
          }

          /* Instruction(address, opcode) */
          else if (arg1 && arg2 && (PyLong_Check(arg1) || PyInt_Check(arg1)) && PyBytes_Check(arg2)) {
            triton::uint64 addr = PyLong_AsUint64(arg1);
            triton::uint8* opc  = reinterpret_cast<triton::uint8*>(PyBytes_AsString(arg2));
            triton::uint32 size = static_cast<triton::uint32>(PyBytes_Size(arg2));
            return PyInstruction(addr, opc, size);
          }

          else {
            return PyErr_Format(PyExc_TypeError, "Instruction(): Expects bytes as first argument or an integer as first and bytes as second argument.");
          }
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_MemoryAccess(PyObject* self, PyObject* args) {
        PyObject* address       = nullptr;
        PyObject* size          = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|OO", &address, &size) == false) {
          return PyErr_Format(PyExc_TypeError, "MemoryAccess(): Invalid constructor.");
        }

        /* Check if the first arg is a integer */
        if (address == nullptr || (!PyLong_Check(address) && !PyInt_Check(address)))
          return PyErr_Format(PyExc_TypeError, "MemoryAccess(): Expects an integer as first argument.");

        /* Check if the second arg is a integer */
        if (size == nullptr || (!PyLong_Check(size) && !PyInt_Check(size)))
          return PyErr_Format(PyExc_TypeError, "MemoryAccess(): Expects an integer as second argument.");

        try {
          triton::arch::MemoryAccess mem(PyLong_AsUint64(address), PyLong_AsUint32(size));
          return PyMemoryAccess(mem);
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_TritonContext(PyObject* self, PyObject* args) {
        PyObject* arch = nullptr;

        /* Extract arguments */
        if (PyArg_ParseTuple(args, "|O", &arch) == false) {
          return PyErr_Format(PyExc_TypeError, "TritonContext(): Invalid constructor.");
        }

        try {
          if (arch == nullptr) {
            return PyTritonContext();
          }
          if (arch == nullptr && (!PyLong_Check(arch) && !PyInt_Check(arch))) {
            return PyErr_Format(PyExc_TypeError, "TritonContext(): Invalid type of argument.");
          }
          return PyTritonContext(static_cast<triton::arch::architecture_e>(PyLong_AsUint32(arch)));
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      static PyObject* triton_AstNode(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "AstNode(): AstNode cannot be directly constructed. Use AstContext instead.");
      }


      static PyObject* triton_AstContext(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "AstContext(): AstContext cannot be directly constructed. Use TritonContext.getAstContext() instead.");
      }


      static PyObject* triton_SymbolicExpression(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "SymbolicExpression(): SymbolicExpression cannot be directly constructed.");
      }


      static PyObject* triton_SymbolicVariable(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "SymbolicVariable(): SymbolicVariable cannot be directly constructed. Use TritonContext.newSymbolicVariable() instead.");
      }


      static PyObject* triton_PathConstraint(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "PathConstraint(): PathConstraint cannot be directly constructed.");
      }


      static PyObject* triton_SolverModel(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "SolverModel(): SolverModel cannot be directly constructed.");
      }


      static PyObject* triton_Register(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "Register(): Register cannot be directly constructed. Use TritonContext.getRegister() instead.");
      }


      static PyObject* triton_BitsVector(PyObject* self, PyObject* args) {
        return PyErr_Format(PyExc_TypeError, "BitsVector(): BitsVector cannot be directly constructed.");
      }


      PyMethodDef tritonCallbacks[] = {
        {"AstContext",          (PyCFunction)triton_AstContext,           METH_VARARGS,   ""},
        {"AstNode",             (PyCFunction)triton_AstNode,              METH_VARARGS,   ""},
        {"BasicBlock",          (PyCFunction)triton_BasicBlock,           METH_VARARGS,   ""},
        {"BitsVector",          (PyCFunction)triton_BitsVector,           METH_VARARGS,   ""},
        {"Immediate",           (PyCFunction)triton_Immediate,            METH_VARARGS,   ""},
        {"Instruction",         (PyCFunction)triton_Instruction,          METH_VARARGS,   ""},
        {"MemoryAccess",        (PyCFunction)triton_MemoryAccess,         METH_VARARGS,   ""},
        {"PathConstraint",      (PyCFunction)triton_PathConstraint,       METH_VARARGS,   ""},
        {"Register",            (PyCFunction)triton_Register,             METH_VARARGS,   ""},
        {"SolverModel",         (PyCFunction)triton_SolverModel,          METH_VARARGS,   ""},
        {"SymbolicExpression",  (PyCFunction)triton_SymbolicExpression,   METH_VARARGS,   ""},
        {"SymbolicVariable",    (PyCFunction)triton_SymbolicVariable,     METH_VARARGS,   ""},
        {"TritonContext",       (PyCFunction)triton_TritonContext,        METH_VARARGS,   ""},
        {nullptr,               nullptr,                                  0,              nullptr}
      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
