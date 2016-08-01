//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <callbacks.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>



/*! \page py_CALLBACK_page CALLBACK
    \brief [**python api**] All information about the CALLBACK python namespace.

\tableofcontents

\section CALLBACK_py_description Description
<hr>

The CALLBACK namespace contains all kinds of callbacks.

\subsection CALLBACK_py_example Example

~~~~~~~~~~~~~{.py}
>>> addCallback(your_function, CALLBACK.MEMORY_HIT)
~~~~~~~~~~~~~

\section CALLBACK_py_api Python API - Items of the CALLBACK namespace
<hr>

- **CALLBACK.MEMORY_HIT**<br>
Defines a callback which be called each time that a memory cell will be hit. The callback takes as uniq argument
an address as integer and returns nothing.

- **CALLBACK.SYMBOLIC_SIMPLIFICATION**<br>
Defines a callback which be called before all symbolic assignments. The callback takes as uniq argument
an \ref py_AstNode_page and must return a valid \ref py_AstNode_page. The returned node is used as assignment.
See also the page about \ref SMT_simplification_page.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initCallbackNamespace(PyObject* callbackDict) {
        PyDict_SetItemString(callbackDict, "MEMORY_HIT",              PyLong_FromUint32(triton::callbacks::MEMORY_HIT));
        PyDict_SetItemString(callbackDict, "SYMBOLIC_SIMPLIFICATION", PyLong_FromUint32(triton::callbacks::SYMBOLIC_SIMPLIFICATION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
