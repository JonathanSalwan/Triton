//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#if defined(__unix__) || defined(__APPLE__)
  #include <dlfcn.h>
#endif

#ifdef __STDC_LIB_EXT1__
#define __STDC_WANT_LIB_EXT1__
#endif
#include <cstdio>

#ifndef __STDC_LIB_EXT1__
int fopen_s(FILE** fd, const char* fn, const char* flags) {
  *fd = fopen(fn, flags);
  if(*fd == 0)
    return -1;
  else
    return 0;
}
#endif

#include <iostream>
#include <stdexcept>
#include <string>

/* libTriton */
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>

/* pintool */
#include "bindings.hpp"



/*! \page py_INSERT_POINT_page INSERT_POINT
    \brief [**python api**] All information about the INSERT_POINT python namespace.

\tableofcontents
\section INSERT_POINT_py_description Description
<hr>

This namespace come from the `pintool` module. The INSERT_POINT namespace contains all kinds of insert points.
An insert point is used to define callbacks at specific points during the execution.

\section INSERT_POINT_py_api Python API - Items of the INSERT_POINT namespace
<hr>

- **INSERT_POINT.AFTER**<br>
Defines an insert point after the instruction processing. At this point, the instruction has been executed. The callback
receives the \ref py_Instruction_page class as argument.

- **INSERT_POINT.BEFORE**<br>
Defines an insert point before the instruction processing. At this point, the IR and data flow were been setup. The callback
receives the \ref py_Instruction_page class as argument.

- **INSERT_POINT.BEFORE_SYMPROC**<br>
Defines an insert point before the symbolic processing. Mainly used to setup and control the data flow as well as the taint spread.
The callback receives the \ref py_Instruction_page class as argument.

- **INSERT_POINT.FINI**<br>
Defines an insert point at the end of the execution. The callback receives any argument.

- **INSERT_POINT.ROUTINE_ENTRY**<br>
Defines an insert point at the entry of a specified routine. The callback receives a `ThreadId` as unique argument.

- **INSERT_POINT.ROUTINE_EXIT**<br>
Defines an insert point at the exit of a specified routine. The callback receives a `ThreadId` as unique argument.

- **INSERT_POINT.IMAGE_LOAD**<br>
Defines an insert point when a new image is loaded. The callback receives an `imagePath` as first argument, an `imageBase` as second
argument and an `imageSize` as third argument.

- **INSERT_POINT.SIGNALS**<br>
Defines an insert point when a signal occurs. The callback receives a `ThreadId` as first argument and a `signalId` as second argument.

- **INSERT_POINT.SYSCALL_ENTRY**<br>
Defines an insert point before each syscall processing. The callback receives a `ThreadId` as first argument and the \ref py_STANDARD_page as second argument.

- **INSERT_POINT.SYSCALL_EXIT**<br>
Defines an insert point after each syscall processing. The callback receives a `ThreadId` as first argument and the \ref py_STANDARD_page as second argument.

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
      std::set<triton::__uint>           startAnalysisFromAddress;
      std::set<triton::__uint>           startAnalysisFromOffset;
      std::set<triton::__uint>           stopAnalysisFromAddress;
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

      /* Create the INSERT_POINT class */
      PyObject *idCallbackClassName = triton::bindings::python::xPyString_FromString("INSERT_POINT");
      PyObject *idCallbackClassDict = triton::bindings::python::xPyDict_New();

      /* Add callback ref into the INSERT_POINT class namespace */
      PyDict_SetItemString(idCallbackClassDict, "AFTER",            triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_AFTER));
      PyDict_SetItemString(idCallbackClassDict, "BEFORE",           triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_BEFORE));
      PyDict_SetItemString(idCallbackClassDict, "BEFORE_SYMPROC",   triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_BEFORE_SYMPROC));
      PyDict_SetItemString(idCallbackClassDict, "FINI",             triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_FINI));
      PyDict_SetItemString(idCallbackClassDict, "ROUTINE_ENTRY",    triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_ROUTINE_ENTRY));
      PyDict_SetItemString(idCallbackClassDict, "ROUTINE_EXIT",     triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_ROUTINE_EXIT));
      PyDict_SetItemString(idCallbackClassDict, "SIGNALS",          triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_SIGNALS));
      PyDict_SetItemString(idCallbackClassDict, "SYSCALL_ENTRY",    triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_SYSCALL_ENTRY));
      PyDict_SetItemString(idCallbackClassDict, "SYSCALL_EXIT",     triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_SYSCALL_EXIT));
      PyDict_SetItemString(idCallbackClassDict, "IMAGE_LOAD",       triton::bindings::python::PyLong_FromUint32(tracer::pintool::options::CB_IMAGE_LOAD));

      /* Create the INSERT_POINT class */
      PyObject *idCallbackClass = triton::bindings::python::xPyClass_New(nullptr, idCallbackClassDict, idCallbackClassName);

      /* ======================= */

      /* Create the STANDARD class */
      PyObject *idStandardClassName = triton::bindings::python::xPyString_FromString("STANDARD");
      PyObject *idStandardClassDict = triton::bindings::python::xPyDict_New();

      /* Add callback ref into the STANDARD class namespace */
      PyDict_SetItemString(idStandardClassDict, "STANDARD_INVALID",             triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_INVALID));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_LINUX",          triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32_LINUX));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32E_LINUX",         triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32E_LINUX));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_MAC",            triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32_MAC));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32E_MAC",           triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32E_MAC));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_WINDOWS_FAST",   triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32_WINDOWS_FAST));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32E_WINDOWS_FAST",  triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32E_WINDOWS_FAST));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_IA32_WINDOWS_ALT",    triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_IA32_WINDOWS_ALT));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_WOW64",               triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_WOW64));
      PyDict_SetItemString(idStandardClassDict, "STANDARD_WINDOWS_INT",         triton::bindings::python::PyLong_FromUint32(LEVEL_CORE::SYSCALL_STANDARD_WINDOWS_INT));

      /* Create the STANDARD class */
      PyObject *idStandardClass = triton::bindings::python::xPyClass_New(nullptr, idStandardClassDict, idStandardClassName);

      /* ======================= */

      /* Add namespace into the pintool module */
      PyModule_AddObject(pintoolModule, "INSERT_POINT", idCallbackClass);
      PyModule_AddObject(pintoolModule, "STANDARD", idStandardClass);
    }


    bool execScript(const char *fileName) {
      #if defined(__unix__) || defined(__APPLE__)
      /* On some Linux distro, we must load libpython to successfully load all others modules. See issue #276. */
      void* handle = dlopen(PYTHON_LIBRARIES, RTLD_LAZY | RTLD_GLOBAL);
      if (!handle)
        throw std::runtime_error("tracer::pintool::execScript(): Cannot load the Python library.");
      #endif

      FILE* fd = nullptr;
      auto err = fopen_s(&fd, fileName, "r");
      if (err != 0)
        throw std::runtime_error("tracer::pintool::execScript(): Script file can't be found.");

      PyRun_SimpleFile(fd, fileName);

      fclose(fd);
      return true;
    }

  };
};

