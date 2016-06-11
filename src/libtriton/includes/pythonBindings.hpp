//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#ifndef TRITONPYTHONBINDINGS_H
#define TRITONPYTHONBINDINGS_H

#include "tritonExport.hpp"

#if defined(__unix__) || defined(__APPLE__)
  #include <python2.7/Python.h>
  #include <python2.7/longintrepr.h>
#elif _WIN32
  #include <Python.h>
  #include <longintrepr.h>
#endif



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Bindings namespace
  namespace bindings {
  /*!
   *  \ingroup triton
   *  \addtogroup bindings
   *  @{
   */

    //! \module The Python namespace
    namespace python {
    /*!
     *  \ingroup bindings
     *  \addtogroup python
     *  @{
     */

      //! Indicates if the python bindings is initialized.
      extern TRITON_EXPORT bool initialized;

      //! CPUSIZE python dict.
      extern TRITON_EXPORT PyObject* cpuSizeDict;

      //! OPCODE python dict.
      extern TRITON_EXPORT PyObject* opcodesDict;

      //! PREFIX python dict.
      extern TRITON_EXPORT PyObject* prefixesDict;

      //! REG python dict.
      extern TRITON_EXPORT PyObject* registersDict;

      #if defined(__unix__) || defined(__APPLE__)
      //! SYSCALL python dict.
      extern TRITON_EXPORT PyObject* syscallsDict;
      #endif

      //! ast python module.
      extern TRITON_EXPORT PyObject* astModule;

      //! triton python module.
      extern TRITON_EXPORT PyObject* tritonModule;

      //! triton python methods.
      extern TRITON_EXPORT PyMethodDef tritonCallbacks[];

      //! ast python methods.
      extern TRITON_EXPORT PyMethodDef astCallbacks[];

      //! Initializes the ARCH python namespace.
      TRITON_EXPORT void initArchNamespace(PyObject* archDict);

      //! Initializes the AST_NODE python namespace.
      TRITON_EXPORT void initAstNodeNamespace(PyObject* astNodeDict);

      //! Initializes the AST_REPRESENTATION python namespace.
      TRITON_EXPORT void initAstRepresentationNamespace(PyObject* astRepresentationDict);

      //! Initializes the CPUSIZE python namespace.
      TRITON_EXPORT void initCpuSizeNamespace(void);

      //! Initializes the REG python namespace.
      TRITON_EXPORT void initRegNamespace(void);

      //! Initializes the OPCODE python namespace.
      TRITON_EXPORT void initX86OpcodesNamespace(void);

      //! Initializes the PREFIX python namespace.
      TRITON_EXPORT void initX86PrefixesNamespace(void);

      //! Initializes the OPERAND python namespace.
      TRITON_EXPORT void initOperandNamespace(PyObject* operandDict);

      //! Initializes the OPTIMIZATION python namespace.
      TRITON_EXPORT void initSymOptiNamespace(PyObject* symOptiDict);

      //! Initializes the SYMEXPR python namespace.
      TRITON_EXPORT void initSymExprNamespace(PyObject* symExprDict);

      #if defined(__unix__) || defined(__APPLE__)
      //! Initializes the SYSCALL python namespace.
      TRITON_EXPORT void initSyscallNamespace(void);
      #endif

      //! Initializes the VERSION python namespace.
      TRITON_EXPORT void initVersionNamespace(PyObject* versionDict);

      //! Entry point python bindings.
      PyMODINIT_FUNC inittriton(void);

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONPYTHONBINDINGS_H */
#endif /* TRITON_PYTHON_BINDINGS */
