//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#ifndef TRITONPYTHONBINDINGS_H
#define TRITONPYTHONBINDINGS_H

#if defined(__unix__) || defined(__APPLE__)
  #include <python2.7/Python.h>
  #include <python2.7/longintrepr.h>
#elif _WIN32
  #include <Python.h>
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
      extern bool initialized;

      //! CPUSIZE python dict.
      extern PyObject* cpuSizeDict;

      //! OPCODE python dict.
      extern PyObject* opcodesDict;

      //! PREFIX python dict.
      extern PyObject* prefixesDict;

      //! REG python dict.
      extern PyObject* registersDict;

      #if defined(__unix__) || defined(__APPLE__)
      //! SYSCALL python dict.
      extern PyObject* syscallsDict;
      #endif

      //! ast python module.
      extern PyObject* astModule;

      //! triton python module.
      extern PyObject* tritonModule;

      //! triton python methods.
      extern PyMethodDef tritonCallbacks[];

      //! ast python methods.
      extern PyMethodDef astCallbacks[];

      //! Initializes the ARCH python namespace.
      void initArchNamespace(PyObject* archDict);

      //! Initializes the AST_NODE python namespace.
      void initAstNodeNamespace(PyObject* astNodeDict);

      //! Initializes the AST_REPRESENTATION python namespace.
      void initAstRepresentationNamespace(PyObject* astRepresentationDict);

      //! Initializes the CPUSIZE python namespace.
      void initCpuSizeNamespace(void);

      //! Initializes the REG python namespace.
      void initRegNamespace(void);

      //! Initializes the OPCODE python namespace.
      void initX86OpcodesNamespace(void);

      //! Initializes the PREFIX python namespace.
      void initX86PrefixesNamespace(void);

      //! Initializes the OPERAND python namespace.
      void initOperandNamespace(PyObject* operandDict);

      //! Initializes the OPTIMIZATION python namespace.
      void initSymOptiNamespace(PyObject* symOptiDict);

      //! Initializes the SYMEXPR python namespace.
      void initSymExprNamespace(PyObject* symExprDict);

      #if defined(__unix__) || defined(__APPLE__)
      //! Initializes the SYSCALL python namespace.
      void initSyscallNamespace(void);
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
#endif /* TRITON_PYTHON_BINDINGS */
