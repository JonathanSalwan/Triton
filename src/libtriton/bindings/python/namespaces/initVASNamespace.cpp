//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/archEnums.hpp>



/*! \page py_VAS_page VAS
    \brief [**python api**] All information about the VAS Python namespace.

\tableofcontents

\section VAS_py_description Description
<hr>

The VAS namespace contains all kinds of vector arrangement specifier.

\section VAS_py_api Python API - Items of the VAS namespace
<hr>

- **VAS.ARM.INVALID**<br>
Invalid vector arrangement specifier.

- **VAS.ARM.v16B**<br>
16 lanes, each containing an 8-bit element.

- **VAS.ARM.v8B**<br>
8 lanes, each containing an 8-bit element.

- **VAS.ARM.v8H**<br>
8 lanes, each containing a 16-bit element.

- **VAS.ARM.v4H**<br>
4 lanes, each containing a 16-bit element.

- **VAS.ARM.v4S**<br>
4 lanes, each containing a 32-bit element.

- **VAS.ARM.v2S**<br>
2 lanes, each containing a 32-bit element.

- **VAS.ARM.v2D**<br>
2 lanes, each containing a 64-bit element.

- **VAS.ARM.v1D**<br>
1 lane containing a 64-bit element.

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initVASNamespace(PyObject* vasDict) {
        PyDict_Clear(vasDict);

        PyObject* armVASDict = xPyDict_New();

        xPyDict_SetItemString(armVASDict, "INVALID", PyLong_FromUint32(triton::arch::arm::ID_VAS_INVALID));
        xPyDict_SetItemString(armVASDict, "v16B",     PyLong_FromUint32(triton::arch::arm::ID_VAS_16B));
        xPyDict_SetItemString(armVASDict, "v8B",      PyLong_FromUint32(triton::arch::arm::ID_VAS_8B));
        xPyDict_SetItemString(armVASDict, "v8H",      PyLong_FromUint32(triton::arch::arm::ID_VAS_8H));
        xPyDict_SetItemString(armVASDict, "v4H",      PyLong_FromUint32(triton::arch::arm::ID_VAS_4H));
        xPyDict_SetItemString(armVASDict, "v4S",      PyLong_FromUint32(triton::arch::arm::ID_VAS_4S));
        xPyDict_SetItemString(armVASDict, "v2S",      PyLong_FromUint32(triton::arch::arm::ID_VAS_2S));
        xPyDict_SetItemString(armVASDict, "v2D",      PyLong_FromUint32(triton::arch::arm::ID_VAS_2D));
        xPyDict_SetItemString(armVASDict, "v1D",      PyLong_FromUint32(triton::arch::arm::ID_VAS_1D));

        PyObject* armVASDictClass = xPyClass_New(nullptr, armVASDict, xPyString_FromString("ARM"));
        xPyDict_SetItemString(vasDict, "ARM", armVASDictClass);
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
