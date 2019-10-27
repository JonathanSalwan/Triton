//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITONPYTHONBINDINGS_H
#define TRITONPYTHONBINDINGS_H

#include <triton/triton_export.h>
#include <Python.h>
#include <longintrepr.h>
#if _WIN32
  #include <cmath>
  #define _hypot hypot
#endif

#include <triton/py3c_compat.h>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Bindings namespace
  namespace bindings {
  /*!
   *  \ingroup triton
   *  \addtogroup bindings
   *  @{
   */

    //! The Python namespace
    namespace python {
    /*!
     *  \ingroup bindings
     *  \addtogroup python
     *  @{
     */

      //! triton python module.
      TRITON_EXPORT extern PyObject* tritonModule;

      //! triton python module definition.
      TRITON_EXPORT extern PyModuleDef tritonModuleDef;

      //! triton python methods.
      TRITON_EXPORT extern PyMethodDef tritonCallbacks[];

      //! Initializes the ARCH python namespace.
      TRITON_EXPORT void initArchNamespace(PyObject* archDict);

      //! Initializes the AST_NODE python namespace.
      TRITON_EXPORT void initAstNodeNamespace(PyObject* astNodeDict);

      //! Initializes the AST_REPRESENTATION python namespace.
      TRITON_EXPORT void initAstRepresentationNamespace(PyObject* astRepresentationDict);

      //! Initializes the CALLBACK python namespace.
      TRITON_EXPORT void initCallbackNamespace(PyObject* callbackDict);

      //! Initializes the CONDITION python namespace.
      TRITON_EXPORT void initConditionsNamespace(PyObject* conditionsDict);

      //! Initializes the CPUSIZE python namespace.
      TRITON_EXPORT void initCpuSizeNamespace(PyObject* cpuSizeDict);

      //! Initializes the OPCODE python namespace.
      TRITON_EXPORT void initOpcodesNamespace(PyObject* opcodeDict);

      //! Initializes the PREFIX python namespace.
      TRITON_EXPORT void initPrefixesNamespace(PyObject* prefixDict);

      //! Initializes the OPERAND python namespace.
      TRITON_EXPORT void initOperandNamespace(PyObject* operandDict);

      //! Initializes the SHIFT python namespace.
      TRITON_EXPORT void initShiftsNamespace(PyObject* shiftDict);

      //! Initializes the EXTEND python namespace.
      TRITON_EXPORT void initExtendNamespace(PyObject* extendDict);

      //! Initializes the REG python namespace.
      TRITON_EXPORT void initRegNamespace(PyObject* regDict);

      //! Initializes the MODE python namespace.
      TRITON_EXPORT void initModeNamespace(PyObject* modeDict);

      //! Initializes the SYMBOLIC python namespace.
      TRITON_EXPORT void initSymbolicNamespace(PyObject* symbolicDict);

      #if defined(__unix__) || defined(__APPLE__)
      //! Initializes the SYSCALL32 python namespace.
      TRITON_EXPORT void initSyscall64Namespace(PyObject* sys64Dict);

      #if defined(__unix__)
      //! Initializes the SYSCALL32 python namespace.
      TRITON_EXPORT void initSyscall32Namespace(PyObject* sys32Dict);
      #endif
      #endif

      //! Initializes the VERSION python namespace.
      TRITON_EXPORT void initVersionNamespace(PyObject* versionDict);

      // workaround for the fact that PyMODINIT_FUNC also generates
      // a declspec(dllexport) and we get a warning about duplication
      #if _WIN32
      #define TRITON_EXPORT_NO_WIN32
      #else
      #define TRITON_EXPORT_NO_WIN32 TRITON_EXPORT
      #endif

      //! Entry point python bindings (Py2/3).
      #if IS_PY3
      PyMODINIT_FUNC TRITON_EXPORT_NO_WIN32 PyInit_triton(void);
      #else
      PyMODINIT_FUNC TRITON_EXPORT_NO_WIN32 inittriton(void);
      TRITON_EXPORT PyObject* PyInit_triton(void);
      #endif

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONPYTHONBINDINGS_H */
