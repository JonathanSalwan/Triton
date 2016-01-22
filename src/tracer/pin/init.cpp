//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <iostream>
#include <stdexcept>
#include <string>

/* libTriton */
#include <pythonUtils.hpp>
#include <pythonXFunctions.hpp>

/* pintool */
#include "bindings.hpp"



/*! \page py_CALLBACK_page CALLBACK
    \brief [**python api**] All information about the CALLBACK python namespace.

\tableofcontents
\section CALLBACK_py_description Description
<hr>

This namespace come from the `pintool` module. The CALLBACK namespace contains all kinds of callback.

\section CALLBACK_py_api Python API - Items of the CALLBACK namespace
<hr>

- **CALLBACK.AFTER**<br>
Defines a callback after the instruction processing. At this point, the instruction has been executed. This callback receives the \py_Instruction_page class as argument.

- **CALLBACK.BEFORE**<br>
Defines a callback before the instruction processing. At this point, the IR and data flow were been setup. This callback receives the \py_Instruction_page class as argument.

- **CALLBACK.BEFORE_SYMPROC**<br>
Defines a callback before the symbolic processing. Mainly used to setup and control the data flow as well as the taint spread. This callback receives the \py_Instruction_page class as argument.

- **CALLBACK.FINI**<br>
Defines a callback at the end of the execution. This callback receives any argument.

- **CALLBACK.ROUTINE_ENTRY**<br>
Defines a callback at the entry of a specified routine. This callback receives a `ThreadId` as unique argument.

- **CALLBACK.ROUTINE_EXIT**<br>
Defines a callback at the exit of a specified routine. This callback receives a `ThreadId` as unique argument.

- **CALLBACK.IMAGE_LOAD**<br>
Defines a callback when a new image is loaded. This callback receives an `imagePath` as first argument, an `imageBase` as second argument and an `imageSize` as third argument.

- **CALLBACK.SIGNALS**<br>
Defines a callback when a signal occurs. This callback receives a `ThreadId` as first argument and a `signalId` as second argument.

- **CALLBACK.SYSCALL_ENTRY**<br>
Defines a callback before each syscall processing. This callback receives a `ThreadId` as first argument and the \ref py_STANDARD_page as second argument.

- **CALLBACK.SYSCALL_EXIT**<br>
Defines a callback after each syscall processing. This callback receives a `ThreadId` as first argument and the \ref py_STANDARD_page as second argument.

*/


/*! \page py_STANDARD_page STANDARD
    \brief [**python api**] All information about the STANDARD python namespace.

\tableofcontents
\section STANDARD_py_description Description
<hr>

This namespace come from the `pintool` module. The STANDARD namespace contains all kinds of syscall standard.

\section STANDARD_py_api Python API - Items of the STANDARD namespace
<hr>

- **STANDARD.INVALID**
- **STANDARD.IA32_LINUX**
- **STANDARD.IA32E_LINUX**
- **STANDARD.IA32_MAC**
- **STANDARD.IA32E_MAC**
- **STANDARD.IA32_WINDOWS_FAST**
- **STANDARD.IA32E_WINDOWS_FAST**
- **STANDARD.IA32_WINDOWS_ALT**
- **STANDARD.WOW64**
- **STANDARD.WINDOWS_INT**

*/



namespace tracer {
  namespace pintool {

    namespace options {
      PyObject*                          callbackAfter              = nullptr;
      PyObject*                          callbackBefore             = nullptr;
      PyObject*                          callbackBeforeIRProc       = nullptr;
      PyObject*                          callbackFini               = nullptr;
      PyObject*                          callbackImageLoad          = nullptr;
      PyObject*                          callbackSignals            = nullptr;
      PyObject*                          callbackSyscallEntry       = nullptr;
      PyObject*                          callbackSyscallExit        = nullptr;
      bool                               startAnalysisFromEntry     = false;
      char*                              startAnalysisFromSymbol    = nullptr;
      std::list<const char*>             imageBlacklist;
      std::list<const char*>             imageWhitelist;
      std::map<const char*, PyObject*>   callbackRoutineEntry;
      std::map<const char*, PyObject*>   callbackRoutineExit;
      std::set<triton::__uint>           startAnalysisFromAddr;
      std::set<triton::__uint>           startAnalysisFromOffset;
      std::set<triton::__uint>           stopAnalysisFromAddr;
      std::set<triton::__uint>           stopAnalysisFromOffset;
      triton::uint32                     targetThreadId             = -1;
    };


    void initBindings(void) {
      /* Setup pintool bindings */
      PyObject* pintoolModule = Py_InitModule("pintool", tracer::pintool::pintoolCallbacks);

      if (pintoolModule == nullptr) {
        std::cerr << "Failed to initialize the pintool bindings" << std::endl;
        PyErr_Print();
        exit(1);
      }

      /* ======================= */

      /* Create the CALLBACK class */
      PyObject *idCallbackClassName = triton::bindings::python::xPyString_FromString("CALLBACK");
      PyObject *idCallbackClassDict = triton::bindings::python::xPyDict_New();

      /* Add callback ref into the CALLBACK class namespace */
      PyDict_SetItemString(idCallbackClassDict, "AFTER",            triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_AFTER));
      PyDict_SetItemString(idCallbackClassDict, "BEFORE",           triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_BEFORE));
      PyDict_SetItemString(idCallbackClassDict, "BEFORE_SYMPROC",   triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_BEFORE_SYMPROC));
      PyDict_SetItemString(idCallbackClassDict, "FINI",             triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_FINI));
      PyDict_SetItemString(idCallbackClassDict, "ROUTINE_ENTRY",    triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_ROUTINE_ENTRY));
      PyDict_SetItemString(idCallbackClassDict, "ROUTINE_EXIT",     triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_ROUTINE_EXIT));
      PyDict_SetItemString(idCallbackClassDict, "SIGNALS",          triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_SIGNALS));
      PyDict_SetItemString(idCallbackClassDict, "SYSCALL_ENTRY",    triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_SYSCALL_ENTRY));
      PyDict_SetItemString(idCallbackClassDict, "SYSCALL_EXIT",     triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_SYSCALL_EXIT));
      PyDict_SetItemString(idCallbackClassDict, "IMAGE_LOAD",       triton::bindings::python::PyLong_FromUint(tracer::pintool::options::CB_IMAGE_LOAD));

      /* Create the CALLBACK class */
      PyObject *idCallbackClass = triton::bindings::python::xPyClass_New(nullptr, idCallbackClassDict, idCallbackClassName);

      /* ======================= */

      /* Create the STANDARD class */
      PyObject *idStandardClassName = triton::bindings::python::xPyString_FromString("STANDARD");
      PyObject *idStandardClassDict = triton::bindings::python::xPyDict_New();

      /* Add callback ref into the STANDARD class namespace */
      PyDict_SetItemString(idStandardClassDict, "STANDARD_INVALID",             triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_INVALID));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_LINUX",          triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32_LINUX));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32E_LINUX",         triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32E_LINUX));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_MAC",            triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32_MAC));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32E_MAC",           triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32E_MAC));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_WINDOWS_FAST",   triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32_WINDOWS_FAST));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32E_WINDOWS_FAST",  triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32E_WINDOWS_FAST));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_WINDOWS_ALT",    triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_IA32_WINDOWS_ALT));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_WOW64",               triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_WOW64));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_WINDOWS_INT",         triton::bindings::python::PyLong_FromUint(LEVEL_CORE::SYSCALL_STANDARD_WINDOWS_INT));

      /* Create the STANDARD class */
      PyObject *idStandardClass = triton::bindings::python::xPyClass_New(nullptr, idStandardClassDict, idStandardClassName);

      /* ======================= */

      /* Add namespace into the pintool module */
      PyModule_AddObject(pintoolModule, "CALLBACK", idCallbackClass);
      PyModule_AddObject(pintoolModule, "STANDARD", idStandardClass);
    }


    bool execScript(const char *fileName) {
      FILE *fd = fopen(fileName, "r");
      if (fd == nullptr)
        return false;
      PyRun_SimpleFile(fd, fileName);
      fclose(fd);
      return true;
    }

  };
};

