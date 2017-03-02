//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/callbacks.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_CALLBACK_page CALLBACK
    \brief [**python api**] All information about the CALLBACK python namespace.

\tableofcontents

\section CALLBACK_py_description Description
<hr>

The CALLBACK namespace contains all kinds of callbacks.

\subsection CALLBACK_py_example Example

~~~~~~~~~~~~~{.py}
>>> addCallback(your_function, CALLBACK.GET_CONCRETE_MEMORY_VALUE)
~~~~~~~~~~~~~

\section CALLBACK_py_api Python API - Items of the CALLBACK namespace
<hr>

- **CALLBACK.GET_CONCRETE_MEMORY_VALUE**<br>
The callback takes as unique argument a \ref py_MemoryAccess_page. Callbacks will be called each time that the
Triton library will need a concrete memory value. The callback must return nothing.

- **CALLBACK.GET_CONCRETE_REGISTER_VALUE**<br>
The callback takes as unique argument a \ref py_Register_page. Callbacks will be called each time that the
Triton library will need a concrete register value. The callback must return nothing.

- **CALLBACK.SYMBOLIC_SIMPLIFICATION**<br>
Defines a callback which be called before all symbolic assignments. The callback takes as uniq argument
an \ref py_AstNode_page and must return a valid \ref py_AstNode_page. The returned node is used as assignment.
See also the page about \ref SMT_simplification_page.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initCallbackNamespace(PyObject* callbackDict) {
        PyDict_SetItemString(callbackDict, "GET_CONCRETE_MEMORY_VALUE",   PyLong_FromUint32(triton::callbacks::GET_CONCRETE_MEMORY_VALUE));
        PyDict_SetItemString(callbackDict, "GET_CONCRETE_REGISTER_VALUE", PyLong_FromUint32(triton::callbacks::GET_CONCRETE_REGISTER_VALUE));
        PyDict_SetItemString(callbackDict, "SYMBOLIC_SIMPLIFICATION",     PyLong_FromUint32(triton::callbacks::SYMBOLIC_SIMPLIFICATION));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
