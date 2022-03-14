//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/config.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/version.hpp>



/*! \page py_VERSION_page VERSION
    \brief [**python api**] All information about the VERSION Python namespace.

\tableofcontents

\section VERSION_py_description Description
<hr>

The VERSION namespace contains all version numbers.

\section VERSION_py_api Python API - Items of the VERSION namespace
<hr>

- **VERSION.BUILD**
- **VERSION.MAJOR**
- **VERSION.MINOR**
- **VERSION.BITWUZLA_INTERFACE**
- **VERSION.LLVM_INTERFACE**
- **VERSION.Z3_INTERFACE**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initVersionNamespace(PyObject* versionDict) {
        xPyDict_SetItemString(versionDict, "MAJOR", PyLong_FromUint32(triton::MAJOR));
        xPyDict_SetItemString(versionDict, "MINOR", PyLong_FromUint32(triton::MINOR));
        xPyDict_SetItemString(versionDict, "BUILD", PyLong_FromUint32(triton::BUILD));

        #ifdef TRITON_Z3_INTERFACE
          Py_INCREF(Py_True);
          xPyDict_SetItemString(versionDict, "Z3_INTERFACE", Py_True);
        #else
          Py_INCREF(Py_False);
          xPyDict_SetItemString(versionDict, "Z3_INTERFACE", Py_False);
        #endif

        #ifdef TRITON_BITWUZLA_INTERFACE
          Py_INCREF(Py_True);
          xPyDict_SetItemString(versionDict, "BITWUZLA_INTERFACE", Py_True);
        #else
          Py_INCREF(Py_False);
          xPyDict_SetItemString(versionDict, "BITWUZLA_INTERFACE", Py_False);
        #endif

        #ifdef TRITON_LLVM_INTERFACE
          Py_INCREF(Py_True);
          xPyDict_SetItemString(versionDict, "LLVM_INTERFACE", Py_True);
        #else
          Py_INCREF(Py_False);
          xPyDict_SetItemString(versionDict, "LLVM_INTERFACE", Py_False);
        #endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
