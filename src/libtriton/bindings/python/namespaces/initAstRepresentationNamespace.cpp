//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/astRepresentation.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_AST_REPRESENTATION_page AST_REPRESENTATION
    \brief [**python api**] All information about the AST_REPRESENTATION python namespace.

\tableofcontents

\section AST_REPRESENTATION_py_description Description
<hr>

The AST_REPRESENTATION namespace contains all kinds of AST representation.

\subsection AST_REPRESENTATION_py_example Example

~~~~~~~~~~~~~{.py}
>>> setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
~~~~~~~~~~~~~

\section AST_REPRESENTATION_py_api Python API - Items of the AST_REPRESENTATION namespace
<hr>

- **AST_REPRESENTATION.SMT**<br>
Enabled, all prints of AST expressions will be represented into the SMT2-Lib syntax. This is the default mode.

- **AST_REPRESENTATION.PYTHON**<br>
Enabled, all prints of AST expressions will be represented into the Python syntax.


*/



namespace triton {
  namespace bindings {
    namespace python {

      void initAstRepresentationNamespace(PyObject* astRepresentationDict) {
        PyDict_SetItemString(astRepresentationDict, "SMT",    PyLong_FromUint32(triton::ast::representations::SMT_REPRESENTATION));
        PyDict_SetItemString(astRepresentationDict, "PYTHON", PyLong_FromUint32(triton::ast::representations::PYTHON_REPRESENTATION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
