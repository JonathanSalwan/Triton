//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITONPYTHONBINDINGS_H
#define TRITONPYTHONBINDINGS_H

#include <Python.h>

#if defined(_WIN32) && !defined(__WINE__)
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
      extern PyObject* tritonModule;

      //! triton python module definition.
      extern PyModuleDef tritonModuleDef;

      //! triton python methods.
      extern PyMethodDef tritonCallbacks[];

      //! Initializes the ARCH python namespace.
      void initArchNamespace(PyObject* archDict);

      //! Initializes the AST_NODE python namespace.
      void initAstNodeNamespace(PyObject* astNodeDict);

      //! Initializes the AST_REPRESENTATION python namespace.
      void initAstRepresentationNamespace(PyObject* astRepresentationDict);

      //! Initializes the CALLBACK python namespace.
      void initCallbackNamespace(PyObject* callbackDict);

      //! Initializes the CONDITION python namespace.
      void initConditionsNamespace(PyObject* conditionsDict);

      //! Initializes the CPUSIZE python namespace.
      void initCpuSizeNamespace(PyObject* cpuSizeDict);

      //! Initializes the OPCODE python namespace.
      void initOpcodesNamespace(PyObject* opcodeDict);

      //! Initializes the PREFIX python namespace.
      void initPrefixesNamespace(PyObject* prefixDict);

      //! Initializes the OPERAND python namespace.
      void initOperandNamespace(PyObject* operandDict);

      //! Initializes the SHIFT python namespace.
      void initShiftsNamespace(PyObject* shiftDict);

      //! Initializes the EXCEPTION python namespace.
      void initExceptionNamespace(PyObject* exceptionDict);

      //! Initializes the EXTEND python namespace.
      void initExtendNamespace(PyObject* extendDict);

      //! Initializes the VAS python namespace.
      void initVASNamespace(PyObject* vasDict);

      //! Initializes the REG python namespace.
      void initRegNamespace(PyObject* regDict);

      //! Initializes the MODE python namespace.
      void initModeNamespace(PyObject* modeDict);

      //! Initializes the SOLVER python namespace.
      void initSolverNamespace(PyObject* solverDict);

      //! Initializes the SOLVER_STATE python namespace.
      void initSolverStateNamespace(PyObject* solverStateDict);

      //! Initializes the STUBS python namespace.
      void initStubsNamespace(PyObject* stubsDict);

      //! Initializes the SYMBOLIC python namespace.
      void initSymbolicNamespace(PyObject* symbolicDict);

      //! Initializes the VERSION python namespace.
      void initVersionNamespace(PyObject* versionDict);

      //! Entry point python bindings (Py2/3).
      #if IS_PY3
      PyMODINIT_FUNC PyInit_triton(void);
      #else
      PyMODINIT_FUNC inittriton(void);
      PyObject* PyInit_triton(void);
      #endif

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONPYTHONBINDINGS_H */
