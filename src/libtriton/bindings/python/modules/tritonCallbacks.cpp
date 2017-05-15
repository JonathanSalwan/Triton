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

// FIXME : Move the tracer documentation part in the tracer documentation...



/*! \page py_triton_page Python bindings
    \brief [**python api**] All information about the libTriton's Python API.
    \anchor triton

\section triton_py_api Python API - Methods and namespaces of the triton module
<hr>

This project work using a TritonContext which contains all the required internal state
to simulate your instructions.

You may also find Helpers to wrap more generic concepts.

- \ref py_Elf_page
- \ref py_Immediate_page
- \ref py_Instruction_page
- \ref py_MemoryAccess_page
- \ref py_Pe_page
- \ref py_TritonContext_page


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

- <b>TritonContext getTritonContext()</b><br>
Pintools use a global triton context to do its simulation. You can acces it
using this function.

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


      static PyObject* triton_TritonContext(PyObject* self, PyObject* args) {
        try {
          return PyTritonContext();
        }
        catch (const triton::exceptions::Exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }
      }


      PyMethodDef tritonCallbacks[] = {
        {"Elf",             (PyCFunction)triton_Elf,              METH_O,         ""},
        {"Immediate",       (PyCFunction)triton_Immediate,        METH_VARARGS,   ""},
        {"Instruction",     (PyCFunction)triton_Instruction,      METH_VARARGS,   ""},
        {"MemoryAccess",    (PyCFunction)triton_MemoryAccess,     METH_VARARGS,   ""},
        {"Pe",              (PyCFunction)triton_Pe,               METH_O,         ""},
        {"TritonContext",   (PyCFunction)triton_TritonContext,    METH_VARARGS,   ""},
        {nullptr,           nullptr,                              0,              nullptr}
      };

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

