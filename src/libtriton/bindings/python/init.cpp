//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonXFunctions.hpp>

#include <iostream>



namespace triton {
  namespace bindings {
    namespace python {

      /* Triton module */
      PyObject* tritonModule = nullptr; /* Must be global because may be updated on-the-fly */

#ifdef IS_PY3
      static struct PyModuleDef tritonModuleDef = {
        PyModuleDef_HEAD_INIT,
        "triton",     /* m_name */
        "This is a module for DBA",  /* m_doc */
        -1,                  /* m_size */
        tritonCallbacks,    /* m_methods */
        NULL,                /* m_reload */
        NULL,                /* m_traverse */
        NULL,                /* m_clear */
        NULL,                /* m_free */
      };
#endif

      /* Python entry point */
#ifdef IS_PY3
      PyMODINIT_FUNC PyInit_triton(void) {
#else
      PyMODINIT_FUNC inittriton(void) {
#endif

        /* Init python */
        Py_Initialize();

        /* Create the triton module ================================================================== */

#ifdef IS_PY3
        triton::bindings::python::tritonModule = PyModule_Create(&tritonModuleDef);
#else
        triton::bindings::python::tritonModule = Py_InitModule("triton", tritonCallbacks);
#endif
        if (triton::bindings::python::tritonModule == nullptr) {
          std::cerr << "Failed to initialize the triton bindings" << std::endl;
          PyErr_Print();
          exit(1);
        }

        /* Create the ARCH namespace ================================================================= */

#ifdef IS_PY3
        PyObject* idArchDictClass = initArchNamespace();
#else
        PyObject* archDict = xPyDict_New();
        initArchNamespace(archDict);
        PyObject* idArchDictClass = xPyClass_New(nullptr, archDict, xPyString_FromString("ARCH"));
#endif

        /* Create the AST_NODE namespace ============================================================= */

#ifdef IS_PY3
        PyObject* idAstNodeDictClass = initAstNodeNamespace();
#else
        PyObject* astNodeDict = xPyDict_New();
        initAstNodeNamespace(astNodeDict);
        PyObject* idAstNodeDictClass = xPyClass_New(nullptr, astNodeDict, xPyString_FromString("AST_NODE"));
#endif

        /* Create the AST_REPRESENTATION namespace =================================================== */

#ifdef IS_PY3
        PyObject* idAstRepresentationDictClass = initAstRepresentationNamespace();
#else
        PyObject* astRepresentationDict = xPyDict_New();
        initAstRepresentationNamespace(astRepresentationDict);
        PyObject* idAstRepresentationDictClass = xPyClass_New(nullptr, astRepresentationDict, xPyString_FromString("AST_REPRESENTATION"));
#endif

        /* Create the CALLBACK namespace ============================================================= */

#ifdef IS_PY3
        PyObject* idCallbackDictClass = initCallbackNamespace();
#else
        PyObject* callbackDict = xPyDict_New();
        initCallbackNamespace(callbackDict);
        PyObject* idCallbackDictClass = xPyClass_New(nullptr, callbackDict, xPyString_FromString("CALLBACK"));
#endif

        /* Create the CPUSIZE namespace ============================================================== */

#ifdef IS_PY3
        PyObject* idCpuSizeClass = initCpuSizeNamespace();
#else
        PyObject* cpuSizeDict = xPyDict_New();
        initCpuSizeNamespace(cpuSizeDict);
        PyObject* idCpuSizeClass = xPyClass_New(nullptr, cpuSizeDict, xPyString_FromString("CPUSIZE"));

#endif

        /* Create the OPCODE namespace =============================================================== */

#ifdef IS_PY3
        PyObject* idOpcodesClass = initX86OpcodesNamespace();
#else
        PyObject* opcodesDict = xPyDict_New();
        initX86OpcodesNamespace(opcodesDict);
        PyObject* idOpcodesClass = xPyClass_New(nullptr, opcodesDict, xPyString_FromString("OPCODE"));
#endif

        /* Create the OPERAND namespace ============================================================== */

#ifdef IS_PY3
        PyObject* idOperandClass = initOperandNamespace();
#else
        PyObject* operandDict = xPyDict_New();
        initOperandNamespace(operandDict);
        PyObject* idOperandClass = xPyClass_New(nullptr, operandDict, xPyString_FromString("OPERAND"));
#endif

        /* Create the OPTIMIZATION namespace ========================================================= */

#ifdef IS_PY3
        PyObject* idModeClass = initModeNamespace();
#else
        PyObject* modeDict = xPyDict_New();
        initModeNamespace(modeDict);
        PyObject* idModeClass = xPyClass_New(nullptr, modeDict, xPyString_FromString("MODE"));
#endif

        /* Create the PREFIX namespace =============================================================== */

#ifdef IS_PY3
        PyObject* idPrefixesClass = initX86PrefixesNamespace();
#else
        PyObject* prefixesDict = xPyDict_New();
        initX86PrefixesNamespace(prefixesDict);
        PyObject* idPrefixesClass = xPyClass_New(nullptr, prefixesDict, xPyString_FromString("PREFIX"));
#endif

        /* Create the REG namespace ================================================================== */

#ifdef IS_PY3
        PyObject* idRegClass = initRegNamespace();
#else
        PyObject* registersDict = xPyDict_New();
        initRegNamespace(registersDict);
        PyObject* idRegClass = xPyClass_New(nullptr, registersDict, xPyString_FromString("REG"));
#endif

        /* Create the SYMEXPR namespace ============================================================== */

#ifdef IS_PY3
        PyObject* idSymExprClass = initSymExprNamespace();
#else
        PyObject* symExprDict = xPyDict_New();
        initSymExprNamespace(symExprDict);
        PyObject* idSymExprClass = xPyClass_New(nullptr, symExprDict, xPyString_FromString("SYMEXPR"));
#endif

        /* Create the SYSCALL namespace ============================================================== */
        #if defined(__unix__) || defined(__APPLE__)
#ifdef IS_PY3
        PyObject* idSyscallsClass64 = initSyscall64Namespace();
#else
        PyObject* syscallsDict64 = xPyDict_New();
        initSyscall64Namespace(syscallsDict64);
        PyObject* idSyscallsClass64 = xPyClass_New(nullptr, syscallsDict64, xPyString_FromString("SYSCALL64"));
#endif
        #endif

        #if defined(__unix__)
#ifdef IS_PY3
        PyObject* idSyscallsClass32 = initSyscall32Namespace();
#else
        PyObject* syscallsDict32 = xPyDict_New();
        initSyscall32Namespace(syscallsDict32);
        PyObject* idSyscallsClass32 = xPyClass_New(nullptr, syscallsDict32, xPyString_FromString("SYSCALL32"));
#endif
        #endif

        /* Create the VERSION namespace ============================================================== */

#ifdef IS_PY3
        PyObject* idVersionClass = initVersionNamespace();
#else
        PyObject* versionDict = xPyDict_New();
        initVersionNamespace(versionDict);
        PyObject* idVersionClass = xPyClass_New(nullptr, versionDict, xPyString_FromString("VERSION"));
#endif


        /* Init triton module ======================================================================== */

        /* Add every modules and namespace into the triton module */
        PyModule_AddObject(triton::bindings::python::tritonModule, "ARCH",                idArchDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "AST_NODE",            idAstNodeDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "AST_REPRESENTATION",  idAstRepresentationDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CALLBACK",            idCallbackDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CPUSIZE",             idCpuSizeClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "MODE",                idModeClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPCODE",              idOpcodesClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPERAND",             idOperandClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "PREFIX",              idPrefixesClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "REG",                 idRegClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYMEXPR",             idSymExprClass);
        #if defined(__unix__) || defined(__APPLE__)
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYSCALL64",           idSyscallsClass64);
        #endif
        #if defined(__unix__)
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYSCALL32",           idSyscallsClass32);
        #endif
        PyModule_AddObject(triton::bindings::python::tritonModule, "VERSION",             idVersionClass);

#ifdef IS_PY3
        return triton::bindings::python::tritonModule;
#endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

