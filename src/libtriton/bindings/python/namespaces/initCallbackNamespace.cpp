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
>>> addCallback(your_function, CALLBACK.MEMORY_LOAD)
~~~~~~~~~~~~~

\section CALLBACK_py_api Python API - Items of the CALLBACK namespace
<hr>

- **CALLBACK.MEMORY_LOAD**<br>
The callback takes as arguments an address which representes the memory cell loaded
and his size. Callbacks will be called each time that a memory cell will be loaded.
The callback must return nothing.

- **CALLBACK.REGISTER_GET**<br>
The callback takes as unique argument a \ref py_Register_page which represents
the register which will be read (GET). Callbacks will be called each time that a
concrete register will be read.

- **CALLBACK.SYMBOLIC_SIMPLIFICATION**<br>
Defines a callback which be called before all symbolic assignments. The callback takes as uniq argument
an \ref py_AstNode_page and must return a valid \ref py_AstNode_page. The returned node is used as assignment.
See also the page about \ref SMT_simplification_page.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initCallbackNamespace(PyObject* callbackDict) {
        PyDict_SetItemString(callbackDict, "MEMORY_LOAD",             PyLong_FromUint32(triton::callbacks::MEMORY_LOAD));
        PyDict_SetItemString(callbackDict, "REGISTER_GET",            PyLong_FromUint32(triton::callbacks::REGISTER_GET));
        PyDict_SetItemString(callbackDict, "SYMBOLIC_SIMPLIFICATION", PyLong_FromUint32(triton::callbacks::SYMBOLIC_SIMPLIFICATION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
