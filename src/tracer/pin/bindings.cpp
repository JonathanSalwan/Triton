//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <pin.H>

/* libTriton */
#include <pythonUtils.hpp>
#include <pythonObjects.hpp>
#include <tritonTypes.hpp>

/* pintool */
#include "bindings.hpp"
#include "context.hpp"
#include "snapshot.hpp"



namespace tracer {
  namespace pintool {

    static PyObject* pintool_addCallback(PyObject* self, PyObject* args) {
      PyObject* function = nullptr;
      PyObject* flag = nullptr;
      PyObject* routine = nullptr;

      /* Extract arguments */
      PyArg_ParseTuple(args, "|OOO", &function, &flag, &routine);

      if (function == nullptr || !PyCallable_Check(function))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::addCallback(): Expected a function callback as first argument.");

      /* Check if the second arg is an IDREF.CALLBACK*/
      if (flag == nullptr || (!PyLong_Check(flag) && !PyInt_Check(flag)))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::addCallback(): Expected an CALLBACK (integer) as second argument.");

      if (triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_BEFORE)
        tracer::pintool::options::callbackBefore = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_BEFORE_SYMPROC))
        tracer::pintool::options::callbackBeforeIRProc = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_AFTER))
        tracer::pintool::options::callbackAfter = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_FINI))
        tracer::pintool::options::callbackFini = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_SIGNALS))
        tracer::pintool::options::callbackSignals = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_SYSCALL_ENTRY))
        tracer::pintool::options::callbackSyscallEntry = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_SYSCALL_EXIT))
        tracer::pintool::options::callbackSyscallExit = function;

      else if (triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_IMAGE_LOAD)
        tracer::pintool::options::callbackImageLoad = function;

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_ROUTINE_ENTRY)){
        if (routine == nullptr || !PyString_Check(routine))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::addCallback(): Expected a routine name (string) as third argument.");
        tracer::pintool::options::callbackRoutineEntry.insert(std::pair<const char*,PyObject*>(PyString_AsString(routine), function));
      }

      else if ((triton::bindings::python::PyLong_AsUint(flag) == tracer::pintool::options::CB_ROUTINE_EXIT)){
        if (routine == nullptr || !PyString_Check(routine))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::addCallback(): Expected a routine name (string) as third argument.");
        tracer::pintool::options::callbackRoutineExit.insert(std::pair<const char*,PyObject*>(PyString_AsString(routine), function));
      }

      else
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::addCallback(): Expected an CALLBACK (integer) as second argument.");

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_checkReadAccess(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::checkReadAccess(): Expected an address (integer) as argument");

      if (PIN_CheckReadAccess(reinterpret_cast<void*>(triton::bindings::python::PyLong_AsUint(addr))) == true)
        Py_RETURN_TRUE;

      Py_RETURN_FALSE;
    }


    static PyObject* pintool_checkWriteAccess(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::checkWriteAccess(): Expected an address (integer) as argument");

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
      PyObject* mem = nullptr;
      PyObject* size = nullptr;

      /* Extract arguments */
      PyArg_ParseTuple(args, "|OO", &mem, &size);

      if (mem != nullptr && (PyMemoryOperand_Check(mem) || PyInt_Check(mem) || PyLong_Check(mem))) {

        if (size != nullptr && (!PyInt_Check(size) && !PyLong_Check(size)))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentMemoryValue(): The size must be an integer.");

        try {
          if (PyMemoryOperand_Check(mem))
            triton::bindings::python::PyLong_FromUint128(tracer::pintool::context::getCurrentMemoryValue(*PyMemoryOperand_AsMemoryOperand(mem)));
          else if (size != nullptr) {
            triton::bindings::python::PyLong_FromUint128(tracer::pintool::context::getCurrentMemoryValue(triton::bindings::python::PyLong_AsUint(mem), triton::bindings::python::PyLong_AsUint(size)));
          }
          else
            triton::bindings::python::PyLong_FromUint128(tracer::pintool::context::getCurrentMemoryValue(triton::bindings::python::PyLong_AsUint(mem)));
        }
        catch (const std::exception& e) {
          return PyErr_Format(PyExc_TypeError, "%s", e.what());
        }

      }
      else
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentMemoryValue(): Expected a Memory as first argument.");
    }


    static PyObject* pintool_getCurrentRegisterValue(PyObject* self, PyObject* reg) {
      if (!PyRegisterOperand_Check(reg))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getCurrentRegisterValue(): Expected a REG as argument.");
      try {
        return triton::bindings::python::PyLong_FromUint128(tracer::pintool::context::getCurrentRegisterValue(*PyRegisterOperand_AsRegisterOperand(reg)));
      }
      catch (const std::exception& e) {
        return PyErr_Format(PyExc_TypeError, "%s", e.what());
      }
    }


    static PyObject* pintool_getSyscallArgument(PyObject* self, PyObject* args) {
      PyObject* num = nullptr;
      PyObject* std = nullptr;
      triton::__uint ret;

      /* Extract arguments */
      PyArg_ParseTuple(args, "|OO", &std, &num);

      if (std == nullptr || (!PyLong_Check(std) && !PyInt_Check(std)))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallArgument(): Expected an id (integer) as first argument");

      if (num == nullptr || (!PyLong_Check(num) && !PyInt_Check(num)))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallArgument(): Expected an id (integer) as second argument");

      LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(triton::bindings::python::PyLong_AsUint(std));;
      ret = PIN_GetSyscallArgument(tracer::pintool::context::lastContext, standard, triton::bindings::python::PyLong_AsUint(num));

      return triton::bindings::python::PyLong_FromUint(ret);
    }


    static PyObject* pintool_getSyscallNumber(PyObject* self, PyObject* std) {
      triton::__uint syscallNumber;

      if (!PyLong_Check(std) && !PyInt_Check(std))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallNumber(): Expected an id (integer) as argument");

      LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(triton::bindings::python::PyLong_AsUint(std));;
      syscallNumber = PIN_GetSyscallNumber(tracer::pintool::context::lastContext, standard);

      return triton::bindings::python::PyLong_FromUint(syscallNumber);
    }


    static PyObject* pintool_getSyscallReturn(PyObject* self, PyObject* std) {
      triton::__uint ret;

      if (!PyLong_Check(std) && !PyInt_Check(std))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::getSyscallReturn(): Expected an id (integer) as argument");

      LEVEL_CORE::SYSCALL_STANDARD standard = static_cast<LEVEL_CORE::SYSCALL_STANDARD>(triton::bindings::python::PyLong_AsUint(std));;
      ret = PIN_GetSyscallReturn(tracer::pintool::context::lastContext, standard);

      return triton::bindings::python::PyLong_FromUint(ret);
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
      if (triton::api.getArchitecture() == triton::arch::ARCH_INVALID)
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
      PyObject* mem = nullptr;
      PyObject* value = nullptr;

      /* Extract arguments */
      PyArg_ParseTuple(args, "|OO", &mem, &value);

      if (mem != nullptr && (PyMemoryOperand_Check(mem) || PyInt_Check(mem) || PyLong_Check(mem))) {

        if (value != nullptr && (!PyInt_Check(value) && !PyLong_Check(value)))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentMemoryValue(): The value must be an integer.");

        try {
          if (value != nullptr && PyMemoryOperand_Check(mem))
            tracer::pintool::context::setCurrentMemoryValue(*PyMemoryOperand_AsMemoryOperand(mem), triton::bindings::python::PyLong_AsUint128(value));
          else if (value != nullptr && (PyInt_Check(mem) || PyLong_Check(mem))) {
            triton::uint8 v = static_cast<triton::uint8>(triton::bindings::python::PyLong_AsUint128(value) & 0xff);
            tracer::pintool::context::setCurrentMemoryValue(triton::bindings::python::PyLong_AsUint(mem), v);
          }
          else
            tracer::pintool::context::setCurrentMemoryValue(*PyMemoryOperand_AsMemoryOperand(mem));
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
      PyObject* reg = nullptr;
      PyObject* value = nullptr;

      /* Extract arguments */
      PyArg_ParseTuple(args, "|OO", &reg, &value);

      if (reg != nullptr && PyRegisterOperand_Check(reg)) {
        if (value != nullptr && (!PyInt_Check(value) && !PyLong_Check(value)))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setCurrentRegisterValue(): The value must be an integer.");

        try {
          if (value != nullptr)
            tracer::pintool::context::setCurrentRegisterValue(*PyRegisterOperand_AsRegisterOperand(reg), triton::bindings::python::PyLong_AsUint128(value));
          else
            tracer::pintool::context::setCurrentRegisterValue(*PyRegisterOperand_AsRegisterOperand(reg));
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
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageBlacklist(): Expected a list as first argument");

      /* Check if the arg list contains only string item and insert them in the internal list */
      for (Py_ssize_t i = 0; i < PyList_Size(arg); i++){
        PyObject *item = PyList_GetItem(arg, i);

        if (!PyString_Check(item))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageBlacklist(): The first argument must be a list of image name (string)");

        tracer::pintool::options::imageBlacklist.push_back(PyString_AsString(item));
      }

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_setupImageWhitelist(PyObject* self, PyObject* arg) {
      /* Check if the arg is a list */
      if (!PyList_Check(arg))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageWhitelist(): Expected a list as first argument");

      /* Check if the arg list contains only string item and insert them in the internal list */
      for (Py_ssize_t i = 0; i < PyList_Size(arg); i++){
        PyObject *item = PyList_GetItem(arg, i);

        if (!PyString_Check(item))
          return PyErr_Format(PyExc_TypeError, "tracer::pintool::setupImageWhitelist(): The first argument must be a list of image name (string)");

        tracer::pintool::options::imageWhitelist.push_back(PyString_AsString(item));
      }

      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_startAnalysisFromAddr(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::startAnalysisFromAddr(): Expected an address (integer) as argument");

      tracer::pintool::options::startAnalysisFromAddr.insert(triton::bindings::python::PyLong_AsUint(addr));
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
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::startAnalysisFromOffset(): Expected an offset (integer) as argument");

      tracer::pintool::options::startAnalysisFromOffset.insert(triton::bindings::python::PyLong_AsUint(offset));
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_startAnalysisFromSymbol(PyObject* self, PyObject* name) {
      if (!PyString_Check(name))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::startAnalysisFromSymbol(): Expected a string as argument");

      tracer::pintool::options::startAnalysisFromSymbol = PyString_AsString(name);
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_stopAnalysisFromAddr(PyObject* self, PyObject* addr) {
      if (!PyLong_Check(addr) && !PyInt_Check(addr))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::stopAnalysisFromAddr(): Expected an address (integer) as argument");

      tracer::pintool::options::stopAnalysisFromAddr.insert(triton::bindings::python::PyLong_AsUint(addr));
      Py_INCREF(Py_None);
      return Py_None;
    }


    static PyObject* pintool_stopAnalysisFromOffset(PyObject* self, PyObject* offset) {
      if (!PyLong_Check(offset) && !PyInt_Check(offset))
        return PyErr_Format(PyExc_TypeError, "tracer::pintool::stopAnalysisFromOffset(): Expected an offset (integer) as argument");

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
      {"addCallback",               pintool_addCallback,                METH_VARARGS,   ""},
      {"checkReadAccess",           pintool_checkReadAccess,            METH_O,         ""},
      {"checkWriteAccess",          pintool_checkWriteAccess,           METH_O,         ""},
      {"detachProcess",             pintool_detachProcess,              METH_NOARGS,    ""},
      {"disableSnapshot",           pintool_disableSnapshot,            METH_NOARGS,    ""},
      {"getCurrentMemoryValue",     pintool_getCurrentMemoryValue,      METH_VARARGS,   ""},
      {"getCurrentRegisterValue",   pintool_getCurrentRegisterValue,    METH_O,         ""},
      {"getSyscallArgument",        pintool_getSyscallArgument,         METH_VARARGS,   ""},
      {"getSyscallNumber",          pintool_getSyscallNumber,           METH_O,         ""},
      {"getSyscallReturn",          pintool_getSyscallReturn,           METH_O,         ""},
      {"isSnapshotEnabled",         pintool_isSnapshotEnabled,          METH_NOARGS,    ""},
      {"restoreSnapshot",           pintool_restoreSnapshot,            METH_NOARGS,    ""},
      {"runProgram",                pintool_runProgram,                 METH_NOARGS,    ""},
      {"setCurrentMemoryValue",     pintool_setCurrentMemoryValue,      METH_VARARGS,   ""},
      {"setCurrentRegisterValue",   pintool_setCurrentRegisterValue,    METH_VARARGS,   ""},
      {"setupImageBlacklist",       pintool_setupImageBlacklist,        METH_O,         ""},
      {"setupImageWhitelist",       pintool_setupImageWhitelist,        METH_O,         ""},
      {"startAnalysisFromAddr",     pintool_startAnalysisFromAddr,      METH_O,         ""},
      {"startAnalysisFromEntry",    pintool_startAnalysisFromEntry,     METH_NOARGS,    ""},
      {"startAnalysisFromOffset",   pintool_startAnalysisFromOffset,    METH_O,         ""},
      {"startAnalysisFromSymbol",   pintool_startAnalysisFromSymbol,    METH_O,         ""},
      {"stopAnalysisFromAddr",      pintool_stopAnalysisFromAddr,       METH_O,         ""},
      {"stopAnalysisFromOffset",    pintool_stopAnalysisFromOffset,     METH_O,         ""},
      {"takeSnapshot",              pintool_takeSnapshot,               METH_NOARGS,    ""},
      {nullptr,                     nullptr,                            0,              nullptr}
    };

  };
};

