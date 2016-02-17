//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <astRepresentation.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_AST_REPRESENTATION_page AST_REPRESENTATION
    \brief [**python api**] All information about the AST_REPRESENTATION python namespace.

\tableofcontents

\section AST_REPRESENTATION_py_description Description
<hr>

The AST_REPRESENTATION namespace contains all modes of AST representation.

\section AST_REPRESENTATION_py_api Python API - Items of the AST_REPRESENTATION namespace
<hr>

- **AST_REPRESENTATION.SMT**
- **AST_REPRESENTATION.PYTHON**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initAstRepresentationNamespace(PyObject* astRepresentationDict) {
        PyDict_SetItemString(astRepresentationDict, "SMT",    PyLong_FromUint(triton::ast::representations::SMT_REPRESENTATION));
        PyDict_SetItemString(astRepresentationDict, "PYTHON", PyLong_FromUint(triton::ast::representations::PYTHON_REPRESENTATION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
