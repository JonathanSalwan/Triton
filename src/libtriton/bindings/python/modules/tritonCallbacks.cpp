//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/exceptions.hpp>
#include <triton/bitsVector.hpp>
#include <triton/immediate.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>



/*! \page py_triton_page Python bindings of the libTriton
    \brief [**python api**] All information about the libTriton's Python API.
    \anchor triton

\section triton_py_api Python API - Methods and namespaces of the triton module
<hr>

This project work using a `TritonContext` which contains all the required internal state
to simulate your instructions. You may also find [helpers](https://github.com/JonathanSalwan/Triton/tree/master/src/examples/python)
to wrap more generic concepts.

\subsection triton_py_api_classes Classes

- \ref py_Immediate_page
- \ref py_Instruction_page
- \ref py_MemoryAccess_page
- \ref py_TritonContext_page


\subsection triton_py_api_namespaces Namespaces

- \ref py_ARCH_page
- \ref py_AST_NODE_page
- \ref py_AST_REPRESENTATION_page
- \ref py_CALLBACK_page
- \ref py_CPUSIZE_page
- \ref py_MODE_page
- \ref py_OPCODE_page
- \ref py_OPERAND_page
- \ref py_REG_page
- \ref py_SYMEXPR_page
- \ref py_SYSCALL_page
- \ref py_VERSION_page

*/



namespace triton {
  namespace bindings {
    namespace python {

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

        /* Extract arguments */
        PyArg_ParseTuple(args, "|OO", &address, &size);

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
        try {
          return PyTritonContext();
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      PyMethodDef tritonCallbacks[] = {
        {"Immediate",       (PyCFunction)triton_Immediate,        METH_VARARGS,   ""},
        {"Instruction",     (PyCFunction)triton_Instruction,      METH_VARARGS,   ""},
        {"MemoryAccess",    (PyCFunction)triton_MemoryAccess,     METH_VARARGS,   ""},
        {"TritonContext",   (PyCFunction)triton_TritonContext,    METH_VARARGS,   ""},
        {nullptr,           nullptr,                              0,              nullptr}
      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

