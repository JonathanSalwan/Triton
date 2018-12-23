//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/version.hpp>



/*! \page py_VERSION_page VERSION
    \brief [**python api**] All information about the VERSION python namespace.

\tableofcontents

\section VERSION_py_description Description
<hr>

The VERSION namespace contains all version numbers.

\section VERSION_py_api Python API - Items of the VERSION namespace
<hr>

- **VERSION.MAJOR**
- **VERSION.MINOR**
- **VERSION.BUILD**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initVersionNamespace(PyObject* versionDict) {
        xPyDict_SetItemString(versionDict, "MAJOR", PyLong_FromUint32(triton::MAJOR));
        xPyDict_SetItemString(versionDict, "MINOR", PyLong_FromUint32(triton::MINOR));
        xPyDict_SetItemString(versionDict, "BUILD", PyLong_FromUint32(triton::BUILD));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
