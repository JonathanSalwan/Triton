//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <peEnums.hpp>
#include <pythonBindings.hpp>
#include <pythonUtils.hpp>



/*! \page py_PE_page PE
    \brief [**python api**] All information about the PE python namespace.

\tableofcontents

\section PE_py_description Description
<hr>

The PE namespace contains all enums used by the PE format.

\section PE_py_api Python API - Items of the PE namespace
<hr>

- **PE.IMAGE_FILE_MACHINE_AMD64**
- **PE.IMAGE_FILE_MACHINE_I386**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initPENamespace(PyObject* peDict) {
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_AMD64",       PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_AMD64));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_I386",        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_I386));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
