//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITONPYTHONBINDINGS_H
#define TRITONPYTHONBINDINGS_H

#include <Python.h>
#include <longintrepr.h>
#if _WIN32
  #include <cmath>
  #define _hypot hypot
#endif



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

      //! Initializes the CPUSIZE python namespace.
      void initCpuSizeNamespace(PyObject* cpuSizeDict);

      //! Initializes the ELF python namespace.
      void initElfNamespace(PyObject* elfDict);

      //! Initializes the PE python namespace.
      void initPENamespace(PyObject* peDict);

      //! Initializes the OPCODE python namespace.
      void initX86OpcodesNamespace(PyObject* opcodeDict);

      //! Initializes the PREFIX python namespace.
      void initX86PrefixesNamespace(PyObject* prefixDict);

      //! Initializes the OPERAND python namespace.
      void initOperandNamespace(PyObject* operandDict);

      //! Initializes the REG python namespace.
      void initRegNamespace(PyObject* regDict);

      //! Initializes the MODE python namespace.
      void initModeNamespace(PyObject* modeDict);

      //! Initializes the SYMEXPR python namespace.
      void initSymExprNamespace(PyObject* symExprDict);

      #if defined(__unix__) || defined(__APPLE__)
      //! Initializes the SYSCALL32 python namespace.
      void initSyscall64Namespace(PyObject* sys64Dict);

      #if defined(__unix__)
      //! Initializes the SYSCALL32 python namespace.
      void initSyscall32Namespace(PyObject* sys32Dict);
      #endif
      #endif

      //! Initializes the VERSION python namespace.
      void initVersionNamespace(PyObject* versionDict);

      //! Entry point python bindings.
      PyMODINIT_FUNC inittriton(void);

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONPYTHONBINDINGS_H */
