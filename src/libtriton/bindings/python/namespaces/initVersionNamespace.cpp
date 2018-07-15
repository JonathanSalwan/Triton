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

- **SYMEXPR.MAJOR**
- **SYMEXPR.MINOR**
- **SYMEXPR.BUILD**

*/



namespace triton {
  namespace bindings {
    namespace python {

#ifdef IS_PY3
      NAMESPACE_TYPE(VERSION, VersionNamespace)

      PyObject* initVersionNamespace() {
        PyType_Ready(&VersionNamespace_Type);
        PyObject* versionDict = VersionNamespace_Type.tp_dict;
#else
      void initVersionNamespace(PyObject* versionDict) {
#endif
        xPyDict_SetItemString(versionDict, "MAJOR", PyLong_FromUint32(triton::MAJOR));
        xPyDict_SetItemString(versionDict, "MINOR", PyLong_FromUint32(triton::MINOR));
        xPyDict_SetItemString(versionDict, "BUILD", PyLong_FromUint32(triton::BUILD));
#ifdef IS_PY3
        return _PyObject_New(&VersionNamespace_Type);
#endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
