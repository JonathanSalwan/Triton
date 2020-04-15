//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

/* libTriton */
#include <triton/pythonUtils.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/tritonTypes.hpp>

#include <pin.H>

/* pintool */
#include "api.hpp"
#include "bindings.hpp"
#include "context.hpp"
#include "snapshot.hpp"



/*! \page pintool_py_page Python bindings of the Pintool tracer
    \brief [**python api**] All information about the tracer's Python API.

\section pintool_py_api Python API - Methods and namespaces of the Pintool tracer
<hr>

This project is shipped with a \ref Tracer_page which can be compile with the `cmake` flag `-DPINTOOL=on`.
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

- <b>integer getCurrentRegisterValue(\ref py_Register_page reg)</b><br>
Returns the register value from a \ref py_Register_page.

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

- <b>integer getSyscallReturn(\ref py_STANDARD_page std)</b><br>
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

- <b>void setCurrentMemoryValue(\ref py_MemoryAccess_page mem, integer value)</b><br>
Sets the current memory value from a \ref py_MemoryAccess_page.

- <b>void setCurrentMemoryValue(integer addr, integer value)</b><br>
Sets the current memory value from an address.

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



namespace tracer {
  namespace pintool {

    static PyObject* pintool_checkReadAccess(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::checkReadAccess(): Expected an address (integer) as argument.");

      if (PIN_CheckReadAccess(reinterpret_cast<void*>(triton::bindings::python::PyLong_AsUint(addr))) == true)
        Py_RETURN_TRUE;

      Py_RETURN_FALSE;
    }


    static PyObject* pintool_checkWriteAccess(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::checkWriteAccess(): Expected an address (integer) as argument.");

      if (PIN_CheckWriteAccess(reinterpret_cast<void*>(triton::bindings::python::PyLong_AsUint(addr))) == true)
        Py_RETURN_TRUE;

      Py_RETURN_FALSE;
    }


    static PyObject* pintool_detachProcess(PyObject* self, PyObject* noarg) {
      PIN_Detach();
      tracer::pintool::analysisTrigger.update(false);
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_disableSnapshot(PyObject* self, PyObject* noarg) {
      tracer::pintool::snapshot.disableSnapshot();
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_getCurrentMemoryValue(PyObject* self, PyObject* args) {
      PyObject* mem   = nullptr;
      PyObject* size  = nullptr;

      /* Extract arguments */
      if (PyArg_ParseTuple(args, "|OO", &mem, &size) == false) {
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentMemoryValue(): Invalid number of arguments");
      }

      if (mem != nullptr && (PyMemoryAccess_Check(mem) || PyInt_Check(mem) || PyLong_Check(mem))) {

        if (size != nullptr && (!PyInt_Check(size) && !PyLong_Check(size)))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentMemoryValue(): The size must be an integer.");

        try {
          if (PyMemoryAccess_Check(mem))
            return triton::bindings::python::PyLong_FromUint512(tracer::pintool::context::getCurrentMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem)));
          else if (size != nullptr) {
            return triton::bindings::python::PyLong_FromUint512(tracer::pintool::context::getCurrentMemoryValue(triton::bindings::python::PyLong_AsUint(mem), triton::bindings::python::PyLong_AsUint32(size)));
          }
          else
            return triton::bindings::python::PyLong_FromUint512(tracer::pintool::context::getCurrentMemoryValue(triton::bindings::python::PyLong_AsUint(mem)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

      }

      return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentMemoryValue(): Expected a Memory as first argument.");
    }


    static PyObject* pintool_getCurrentRegisterValue(PyObject* self, PyObject* reg) {
      if (!PyRegister_Check(reg))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentRegisterValue(): Expected a REG as argument.");
      try {
        return triton::bindings::python::PyLong_FromUint512(tracer::pintool::context::getCurrentRegisterValue(*PyRegister_AsRegister(reg)));
      }
      catch (const std::exception& e) {
        return PyErr_Format(PyExc_TypeError, "%s", e.what());
      }
    }


    static PyObject* pintool_getImageName(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getImageName(): Expected an address (integer) as argument.");

      std::string imageName = tracer::pintool::getImageName(triton::bindings::python::PyLong_AsUint(addr));
      return PyStr_FromFormat("%s", imageName.c_str());;
    }


    static PyObject* pintool_getRoutineName(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getImageName(): Expected an address (integer) as argument.");

      std::string routineName = tracer::pintool::getRoutineName(triton::bindings::python::PyLong_AsUint(addr));
      return PyStr_FromFormat("%s", routineName.c_str());;
    }


    static PyObject* pintool_getSyscallArgument(PyObject* self, PyObject* args) {
      PyObject* num = nullptr;
      PyObject* std = nullptr;
      triton::__uint ret;

      /* Extract arguments */
      if (PyArg_ParseTuple(args, "|OO", &std, &num) == false) {
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallArgument(): Invalid number of arguments");
      }

      if (std == nullptr || (!PyLong_Check(std) && !PyInt_Check(std)))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallArgument(): Expected an id (integer) as first argument.");

      if (num == nullptr || (!PyLong_Check(num) && !PyInt_Check(num)))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallArgument(): Expected an id (integer) as second argument.");

      LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(triton::bindings::python::PyLong_AsUint32(std));
      ret = PIN_GetSyscallArgument(tracer::pintool::context::lastContext, standard, triton::bindings::python::PyLong_AsUint32(num));

      return triton::bindings::python::PyLong_FromUint(ret);
    }


    static PyObject* pintool_getSyscallNumber(PyObject* self, PyObject* std) {
      triton::uint32 syscallNumber;

      if (!PyLong_Check(std) && !PyInt_Check(std))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallNumber(): Expected an id (integer) as argument.");

      LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(triton::bindings::python::PyLong_AsUint32(std));
      syscallNumber = PIN_GetSyscallNumber(tracer::pintool::context::lastContext, standard);

      return triton::bindings::python::PyLong_FromUint32(syscallNumber);
    }


    static PyObject* pintool_getSyscallReturn(PyObject* self, PyObject* std) {
      triton::__uint ret;

      if (!PyLong_Check(std) && !PyInt_Check(std))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallReturn(): Expected an id (integer) as argument.");

      LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(triton::bindings::python::PyLong_AsUint32(std));
      ret = PIN_GetSyscallReturn(tracer::pintool::context::lastContext, standard);

      return triton::bindings::python::PyLong_FromUint(ret);
    }


    static PyObject* pintool_getTritonContext(PyObject* self, PyObject* noarg) {
      try {
        return triton::bindings::python::PyTritonContextRef(tracer::pintool::api);
      }
      catch (const std::exception& e) {
        return PyErr_Format(PyExc_TypeError, "%s", e.what());
      }
    }


    static PyObject* pintool_insertCall(PyObject* self, PyObject* args) {
      PyObject* function  = nullptr;
      PyObject* flag      = nullptr;
      PyObject* routine   = nullptr;

      /* Extract arguments */
      if (PyArg_ParseTuple(args, "|OOO", &function, &flag, &routine) == false) {
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::insertCall(): Invalid number of arguments");
      }

      if (function == nullptr || !PyCallable_Check(function))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::insertCall(): Expected a function callback as first argument.");

      /* Check if the second arg is an INSERT_POINT*/
      if (flag == nullptr || (!PyLong_Check(flag) && !PyInt_Check(flag)))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::insertCall(): Expected an INSERT_POINT (integer) as second argument.");

      if (triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_BEFORE)
        tracer::pintool::options::callbackBefore = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_BEFORE_SYMPROC))
        tracer::pintool::options::callbackBeforeIRProc = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_AFTER))
        tracer::pintool::options::callbackAfter = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_FINI))
        tracer::pintool::options::callbackFini = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_SIGNALS))
        tracer::pintool::options::callbackSignals = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_SYSCALL_ENTRY))
        tracer::pintool::options::callbackSyscallEntry = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_SYSCALL_EXIT))
        tracer::pintool::options::callbackSyscallExit = function;

      else if (triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_IMAGE_LOAD)
        tracer::pintool::options::callbackImageLoad = function;

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_ROUTINE_ENTRY)) {
        if (routine == nullptr || !PyStr_Check(routine))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::insertCall(): Expected a routine name (string) as third argument.");
        tracer::pintool::options::callbackRoutineEntry.insert(std::pair<const char*,PyObject*>(PyStr_AsString(routine), function));
      }

      else if ((triton::bindings::python::PyLong_AsUint32(flag) == tracer::pintool::options::CB_ROUTINE_EXIT)) {
        if (routine == nullptr || !PyStr_Check(routine))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::insertCall(): Expected a routine name (string) as third argument.");
        tracer::pintool::options::callbackRoutineExit.insert(std::pair<const char*,PyObject*>(PyStr_AsString(routine), function));
      }

      else
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::insertCall(): Expected an INSERT_POINT (integer) as second argument.");

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_isSnapshotEnabled(PyObject* self, PyObject* noarg) {
      if (tracer::pintool::snapshot.isLocked() == false)
        Py_RETURN_TRUE;
      Py_RETURN_FALSE;
    }


    static PyObject* pintool_restoreSnapshot(PyObject* self, PyObject* noarg) {
      tracer::pintool::snapshot.setRestore(true);
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_runProgram(PyObject* self, PyObject* noarg) {
      /* Check if the architecture is definied */
      if (tracer::pintool::api.getArchitecture() == triton::arch::ARCH_INVALID)
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::runProgram(): Architecture is not defined.");
      /* Never returns - Rock 'n roll baby \o/ */
      try {
        PIN_StartProgram();
      }
      catch (const std::exception& e) {
        return PyErr_Format(PyExc_TypeError, "%s", e.what());
      }
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_setCurrentMemoryValue(PyObject* self, PyObject* args) {
      PyObject* mem   = nullptr;
      PyObject* value = nullptr;

      /* Extract arguments */
      if (PyArg_ParseTuple(args, "|OO", &mem, &value) == false) {
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentMemoryValue(): Invalid number of arguments");
      }

      if (mem != nullptr && (PyMemoryAccess_Check(mem) || PyInt_Check(mem) || PyLong_Check(mem))) {

        if (value == nullptr || (!PyInt_Check(value) && !PyLong_Check(value)))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentMemoryValue(): Expected an integer value as second argument.");

        try {
          if (PyMemoryAccess_Check(mem))
            tracer::pintool::context::setCurrentMemoryValue(*PyMemoryAccess_AsMemoryAccess(mem), triton::bindings::python::PyLong_AsUint512(value));
          else if ((PyInt_Check(mem) || PyLong_Check(mem))) {
            triton::uint8 v = (triton::bindings::python::PyLong_AsUint512(value) & 0xff).convert_to<triton::uint8>();
            tracer::pintool::context::setCurrentMemoryValue(triton::bindings::python::PyLong_AsUint(mem), v);
          }
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

      }
      else
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentMemoryValue(): Expected a Memory as first argument.");

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_setCurrentRegisterValue(PyObject* self, PyObject* args) {
      PyObject* reg   = nullptr;
      PyObject* value = nullptr;

      /* Extract arguments */
      if (PyArg_ParseTuple(args, "|OO", &reg, &value) == false) {
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentRegisterValue(): Invalid number of arguments");
      }

      if (reg != nullptr && PyRegister_Check(reg)) {
        if (value == nullptr || (!PyInt_Check(value) && !PyLong_Check(value)))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentRegisterValue(): Expected an integer value as second argument.");

        try {
          tracer::pintool::context::setCurrentRegisterValue(*PyRegister_AsRegister(reg), triton::bindings::python::PyLong_AsUint512(value));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

      }
      else
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentRegisterValue(): Expected a REG as first argument.");

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_setupImageBlacklist(PyObject* self, PyObject* arg) {
      /* Check if the arg is a list */
      if (!PyList_Check(arg))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageBlacklist(): Expected a list as first argument.");

      /* Check if the arg list contains only string item and insert them in the internal list */
      for (Py_ssize_t i = 0; i < PyList_Size(arg); i++) {
        PyObject* item = PyList_GetItem(arg, i);

        if (!PyStr_Check(item))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageBlacklist(): Each item of the list must be a string.");

        tracer::pintool::options::imageBlacklist.push_back(PyStr_AsString(item));
      }

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_setupImageWhitelist(PyObject* self, PyObject* arg) {
      /* Check if the arg is a list */
      if (!PyList_Check(arg))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageWhitelist(): Expected a list as first argument.");

      /* Check if the arg list contains only string item and insert them in the internal list */
      for (Py_ssize_t i = 0; i < PyList_Size(arg); i++) {
        PyObject* item = PyList_GetItem(arg, i);

        if (!PyStr_Check(item))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageWhitelist(): Each item of the list must be a string.");

        tracer::pintool::options::imageWhitelist.push_back(PyStr_AsString(item));
      }

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_startAnalysisFromAddress(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::startAnalysisFromAddress(): Expected an address (integer) as argument.");

      tracer::pintool::options::startAnalysisFromAddress.insert(triton::bindings::python::PyLong_AsUint(addr));
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_startAnalysisFromEntry(PyObject* self, PyObject* noarg) {
      tracer::pintool::options::startAnalysisFromEntry = true;
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_startAnalysisFromOffset(PyObject* self, PyObject* offset) {
      if (!PyLong_Check(offset) && !PyInt_Check(offset))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::startAnalysisFromOffset(): Expected an offset (integer) as argument.");

      tracer::pintool::options::startAnalysisFromOffset.insert(triton::bindings::python::PyLong_AsUint(offset));
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_startAnalysisFromSymbol(PyObject* self, PyObject* name) {
      if (!PyStr_Check(name))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::startAnalysisFromSymbol(): Expected a string as argument.");

      tracer::pintool::options::startAnalysisFromSymbol = PyStr_AsString(name);
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_stopAnalysisFromAddress(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::stopAnalysisFromAddress(): Expected an address (integer) as argument.");

      tracer::pintool::options::stopAnalysisFromAddress.insert(triton::bindings::python::PyLong_AsUint(addr));
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_stopAnalysisFromOffset(PyObject* self, PyObject* offset) {
      if (!PyLong_Check(offset) && !PyInt_Check(offset))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::stopAnalysisFromOffset(): Expected an offset (integer) as argument.");

      tracer::pintool::options::stopAnalysisFromOffset.insert(triton::bindings::python::PyLong_AsUint(offset));
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_takeSnapshot(PyObject* self, PyObject* noarg) {
      tracer::pintool::snapshot.takeSnapshot(tracer::pintool::context::lastContext);
      Py_INCREF(Py_None);
      return Py_None;
    }


    PyMethodDef pintoolCallbacks[] = {
      {"checkReadAccess",           pintool_checkReadAccess,            METH_O,         ""},
      {"checkWriteAccess",          pintool_checkWriteAccess,           METH_O,         ""},
      {"detachProcess",             pintool_detachProcess,              METH_NOARGS,    ""},
      {"disableSnapshot",           pintool_disableSnapshot,            METH_NOARGS,    ""},
      {"getCurrentMemoryValue",     pintool_getCurrentMemoryValue,      METH_VARARGS,   ""},
      {"getCurrentRegisterValue",   pintool_getCurrentRegisterValue,    METH_O,         ""},
      {"getImageName",              pintool_getImageName,               METH_O,         ""},
      {"getRoutineName",            pintool_getRoutineName,             METH_O,         ""},
      {"getSyscallArgument",        pintool_getSyscallArgument,         METH_VARARGS,   ""},
      {"getSyscallNumber",          pintool_getSyscallNumber,           METH_O,         ""},
      {"getSyscallReturn",          pintool_getSyscallReturn,           METH_O,         ""},
      {"getTritonContext",          pintool_getTritonContext,           METH_NOARGS,    ""},
      {"insertCall",                pintool_insertCall,                 METH_VARARGS,   ""},
      {"isSnapshotEnabled",         pintool_isSnapshotEnabled,          METH_NOARGS,    ""},
      {"restoreSnapshot",           pintool_restoreSnapshot,            METH_NOARGS,    ""},
      {"runProgram",                pintool_runProgram,                 METH_NOARGS,    ""},
      {"setCurrentMemoryValue",     pintool_setCurrentMemoryValue,      METH_VARARGS,   ""},
      {"setCurrentRegisterValue",   pintool_setCurrentRegisterValue,    METH_VARARGS,   ""},
      {"setupImageBlacklist",       pintool_setupImageBlacklist,        METH_O,         ""},
      {"setupImageWhitelist",       pintool_setupImageWhitelist,        METH_O,         ""},
      {"startAnalysisFromAddress",  pintool_startAnalysisFromAddress,   METH_O,         ""},
      {"startAnalysisFromEntry",    pintool_startAnalysisFromEntry,     METH_NOARGS,    ""},
      {"startAnalysisFromOffset",   pintool_startAnalysisFromOffset,    METH_O,         ""},
      {"startAnalysisFromSymbol",   pintool_startAnalysisFromSymbol,    METH_O,         ""},
      {"stopAnalysisFromAddress",   pintool_stopAnalysisFromAddress,    METH_O,         ""},
      {"stopAnalysisFromOffset",    pintool_stopAnalysisFromOffset,     METH_O,         ""},
      {"takeSnapshot",              pintool_takeSnapshot,               METH_NOARGS,    ""},
      {nullptr,                     nullptr,                            0,              nullptr}
    };

  };
};

