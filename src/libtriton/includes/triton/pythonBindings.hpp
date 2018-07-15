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

#ifdef IS_PY3
  #define PyInt_Check PyLong_Check
  #define PyString_Check PyUnicode_Check
  #define PyString_AsString PyUnicode_AsUTF8
  #define PyString_FromFormat PyUnicode_FromFormat
  #define PyString_FromString PyUnicode_FromString
  #define PyInt_AsLong PyLong_AsLong
  
  
  #define NAMESPACE_TYPE(NAME, label) \
  static int label ## _print(PyObject *self) { return 0; } \
  static PyObject* label ## _str(PyObject *self) { \
    return PyString_FromFormat("%s", self->ob_type->tp_name); \
  }\
  PyTypeObject label ## _Type = { \
    PyVarObject_HEAD_INIT(&PyType_Type, 0) \
    #NAME ,                                     /* tp_name */ \
    0,                                          /* tp_basicsize */ \
    0,                                          /* tp_itemsize */ \
    0,                                          /* tp_dealloc */ \
    (printfunc) label ## _print,                /* tp_print */ \
    0,                                          /* tp_getattr */ \
    0,                                          /* tp_setattr */ \
    0,                                          /* tp_compare */ \
    0,                                          /* tp_repr */ \
    0,                                          /* tp_as_number */ \
    0,                                          /* tp_as_sequence */ \
    0,                                          /* tp_as_mapping */ \
    0,                                          /* tp_hash */ \
    0,                                          /* tp_call */ \
    (reprfunc) label ## _str,                   /* tp_str */ \
    0,                                          /* tp_getattro */ \
    0,                                          /* tp_setattro */ \
    0,                                          /* tp_as_buffer */ \
    Py_TPFLAGS_HEAPTYPE,                        /* tp_flags */ \
    #NAME " namespace",                         /* tp_doc */ \
    0,                                          /* tp_traverse */ \
    0,                                          /* tp_clear */ \
    0,                                          /* tp_richcompare */ \
    0,                                          /* tp_weaklistoffset */ \
    0,                                          /* tp_iter */ \
    0,                                          /* tp_iternext */ \
    0,                                          /* tp_methods */ \
    0,                                          /* tp_members */ \
    0,                                          /* tp_getset */ \
    0,                                          /* tp_base */ \
    0,                                          /* tp_dict */ \
    0,                                          /* tp_descr_get */ \
    0,                                          /* tp_descr_set */ \
    0,                                          /* tp_dictoffset */ \
    0,                                          /* tp_init */ \
    0,                                          /* tp_alloc */ \
    0,                                          /* tp_new */ \
    0,                                          /* tp_free */ \
    0,                                          /* tp_is_gc */ \
    0,                                          /* tp_bases */ \
    0,                                          /* tp_mro */ \
    0,                                          /* tp_cache */ \
    0,                                          /* tp_subclasses */ \
    0,                                          /* tp_weaklist */ \
    0,                                          /* tp_del */ \
    0,                                          /* tp_version_tag */ \
    0,                                          /* tp_dealloc */ \
  };
#endif // IS_PY3


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
#ifdef IS_PY3
      PyObject* initArchNamespace();
#else
      void initArchNamespace(PyObject* archDict);
#endif

      //! Initializes the AST_NODE python namespace.
#ifdef IS_PY3
      PyObject* initAstNodeNamespace();
#else
      void initAstNodeNamespace(PyObject* astNodeDict);
#endif

      //! Initializes the AST_REPRESENTATION python namespace.
#ifdef IS_PY3
      PyObject* initAstRepresentationNamespace();
#else
      void initAstRepresentationNamespace(PyObject* astRepresentationDict);
#endif

      //! Initializes the CALLBACK python namespace.
#ifdef IS_PY3
      PyObject* initCallbackNamespace();
#else
      void initCallbackNamespace(PyObject* callbackDict);
#endif

      //! Initializes the CPUSIZE python namespace.
#ifdef IS_PY3
      PyObject* initCpuSizeNamespace();
#else
      void initCpuSizeNamespace(PyObject* cpuSizeDict);
#endif

      //! Initializes the OPCODE python namespace.
#ifdef IS_PY3
      PyObject* initX86OpcodesNamespace();
#else
      void initX86OpcodesNamespace(PyObject* opcodeDict);
#endif

      //! Initializes the PREFIX python namespace.
#ifdef IS_PY3
      PyObject* initX86PrefixesNamespace();
#else
      void initX86PrefixesNamespace(PyObject* prefixDict);
#endif

      //! Initializes the OPERAND python namespace.
#ifdef IS_PY3
      PyObject* initOperandNamespace();
#else
      void initOperandNamespace(PyObject* operandDict);
#endif

      //! Initializes the REG python namespace.
#ifdef IS_PY3
      PyObject* initRegNamespace();
#else
      void initRegNamespace(PyObject* regDict);
#endif

      //! Initializes the MODE python namespace.
#ifdef IS_PY3
      PyObject* initModeNamespace();
#else
      void initModeNamespace(PyObject* modeDict);
#endif

      //! Initializes the SYMEXPR python namespace.
#ifdef IS_PY3
      PyObject* initSymExprNamespace();
#else
      void initSymExprNamespace(PyObject* symExprDict);
#endif

      #if defined(__unix__) || defined(__APPLE__)
      //! Initializes the SYSCALL32 python namespace.
#ifdef IS_PY3
      PyObject* initSyscall64Namespace();
#else
      void initSyscall64Namespace(PyObject* sys64Dict);
#endif

      #if defined(__unix__)
      //! Initializes the SYSCALL32 python namespace.
#ifdef IS_PY3
      PyObject* initSyscall32Namespace();
#else
      void initSyscall32Namespace(PyObject* sys32Dict);
#endif
      #endif
      #endif

      //! Initializes the VERSION python namespace.
#ifdef IS_PY3
      PyObject* initVersionNamespace();
#else
      void initVersionNamespace(PyObject* versionDict);
#endif

      //! Entry point python bindings.
#ifdef IS_PY3
      PyMODINIT_FUNC PyInit_triton(void);
#else
      PyMODINIT_FUNC inittriton(void);
#endif

    /*! @} End of python namespace */
    };
  /*! @} End of bindings namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITONPYTHONBINDINGS_H */
