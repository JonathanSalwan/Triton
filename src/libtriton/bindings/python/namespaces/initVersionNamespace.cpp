//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <operandInterface.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>
#include <version.hpp>



/*! \page py_VERSION_page VERSION
    \brief [**python api**] All information about the VERSION python namespace.

\tableofcontents

\section VERSION_py_description Description
<hr>

The VERSION namespace contains all version numbers.

\section VERSION_py_api Python API - Items of the VERSION namespace
<hr>

- **SYMEXPR.MAJOR**
- **SYMEXPR.MINOR**
- **SYMEXPR.BUILD**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initVersionNamespace(PyObject* versionDict) {
        PyDict_SetItemString(versionDict, "MAJOR", PyLong_FromUint(triton::MAJOR));
        PyDict_SetItemString(versionDict, "MINOR", PyLong_FromUint(triton::MINOR));
        PyDict_SetItemString(versionDict, "BUILD", PyLong_FromUint(triton::BUILD));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
