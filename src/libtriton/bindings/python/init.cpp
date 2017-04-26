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


      /* Python entry point */
      PyMODINIT_FUNC inittriton(void) {

        /* Init python */
        Py_Initialize();

        /* Create the triton module ================================================================== */

        triton::bindings::python::tritonModule = Py_InitModule("triton", tritonCallbacks);
        if (triton::bindings::python::tritonModule == nullptr) {
          std::cerr << "Failed to initialize the triton bindings" << std::endl;
          PyErr_Print();
          exit(1);
        }

        /* Create the ARCH namespace ================================================================= */

        PyObject* archDict = xPyDict_New();
        initArchNamespace(archDict);
        PyObject* idArchDictClass = xPyClass_New(nullptr, archDict, xPyString_FromString("ARCH"));

        /* Create the AST_NODE namespace ============================================================= */

        PyObject* astNodeDict = xPyDict_New();
        initAstNodeNamespace(astNodeDict);
        PyObject* idAstNodeDictClass = xPyClass_New(nullptr, astNodeDict, xPyString_FromString("AST_NODE"));

        /* Create the AST_REPRESENTATION namespace =================================================== */

        PyObject* astRepresentationDict = xPyDict_New();
        initAstRepresentationNamespace(astRepresentationDict);
        PyObject* idAstRepresentationDictClass = xPyClass_New(nullptr, astRepresentationDict, xPyString_FromString("AST_REPRESENTATION"));

        /* Create the CALLBACK namespace ============================================================= */

        PyObject* callbackDict = xPyDict_New();
        initCallbackNamespace(callbackDict);
        PyObject* idCallbackDictClass = xPyClass_New(nullptr, callbackDict, xPyString_FromString("CALLBACK"));

        /* Create the CPUSIZE namespace ============================================================== */

        PyObject* cpuSizeDict = xPyDict_New();
        initCpuSizeNamespace(cpuSizeDict);
        PyObject* idCpuSizeClass = xPyClass_New(nullptr, cpuSizeDict, xPyString_FromString("CPUSIZE"));

        /* Create the OPCODE namespace =============================================================== */

        PyObject* opcodesDict = xPyDict_New();
        initX86OpcodesNamespace(opcodesDict);
        PyObject* idOpcodesClass = xPyClass_New(nullptr, opcodesDict, xPyString_FromString("OPCODE"));

        /* Create the OPERAND namespace ============================================================== */

        PyObject* operandDict = xPyDict_New();
        initOperandNamespace(operandDict);
        PyObject* idOperandClass = xPyClass_New(nullptr, operandDict, xPyString_FromString("OPERAND"));

        /* Create the OPTIMIZATION namespace ========================================================= */

        PyObject* modeDict = xPyDict_New();
        initModeNamespace(modeDict);
        PyObject* idModeClass = xPyClass_New(nullptr, modeDict, xPyString_FromString("MODE"));

        /* Create the PREFIX namespace =============================================================== */

        PyObject* prefixesDict = xPyDict_New();
        initX86PrefixesNamespace(prefixesDict);
        PyObject* idPrefixesClass = xPyClass_New(nullptr, prefixesDict, xPyString_FromString("PREFIX"));

        /* Create the REG namespace ================================================================== */

        PyObject* registersDict = xPyDict_New();
        initRegNamespace(registersDict);
        PyObject* idRegClass = xPyClass_New(nullptr, registersDict, xPyString_FromString("REG"));

        /* Create the SYMEXPR namespace ============================================================== */

        PyObject* symExprDict = xPyDict_New();
        initSymExprNamespace(symExprDict);
        PyObject* idSymExprClass = xPyClass_New(nullptr, symExprDict, xPyString_FromString("SYMEXPR"));

        /* Create the SYSCALL namespace ============================================================== */
        #if defined(__unix__) || defined(__APPLE__)
        PyObject* syscallsDict64 = xPyDict_New();
        initSyscall64Namespace(syscallsDict64);
        PyObject* idSyscallsClass64 = xPyClass_New(nullptr, syscallsDict64, xPyString_FromString("SYSCALL64"));
        #endif

        #if defined(__unix__)
        PyObject* syscallsDict32 = xPyDict_New();
        initSyscall32Namespace(syscallsDict32);
        PyObject* idSyscallsClass32 = xPyClass_New(nullptr, syscallsDict32, xPyString_FromString("SYSCALL32"));
        #endif

        /* Create the VERSION namespace ============================================================== */

        PyObject* versionDict = xPyDict_New();
        initVersionNamespace(versionDict);
        PyObject* idVersionClass = xPyClass_New(nullptr, versionDict, xPyString_FromString("VERSION"));


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
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

