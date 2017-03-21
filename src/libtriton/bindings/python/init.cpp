//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <iostream>

#include <triton/pythonBindings.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/pythonBindings.hpp>



namespace triton {
  namespace bindings {
    namespace python {

      /* Triton module */
      bool      initialized           = false;
      PyObject* astModule             = nullptr; /* Must be global because may be updated on-the-fly */
      PyObject* cpuSizeDict           = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* opcodesDict           = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* prefixesDict          = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* registersDict         = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* tritonModule          = nullptr; /* Must be global because may be updated on-the-fly */
      #if defined(__unix__) || defined(__APPLE__)
      PyObject* syscallsDict          = nullptr; /* Must be global because it's updated on-the-fly */
      #endif


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

        /* Create the ast module ===================================================================== */

        triton::bindings::python::astModule = Py_InitModule("triton.ast", astCallbacks);
        if (triton::bindings::python::astModule == nullptr) {
          std::cerr << "Failed to initialize the ast bindings" << std::endl;
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

        triton::bindings::python::cpuSizeDict = xPyDict_New();
        PyObject* idCpuSizeClass = xPyClass_New(nullptr, triton::bindings::python::cpuSizeDict, xPyString_FromString("CPUSIZE"));

        /* Create the ELF namespace ================================================================== */

        PyObject* elfDict = xPyDict_New();
        initElfNamespace(elfDict);
        PyObject* idElfDictClass = xPyClass_New(nullptr, elfDict, xPyString_FromString("ELF"));

        /* Create the OPCODE namespace =============================================================== */

        triton::bindings::python::opcodesDict = xPyDict_New();
        PyObject* idOpcodesClass = xPyClass_New(nullptr, triton::bindings::python::opcodesDict, xPyString_FromString("OPCODE"));

        /* Create the OPERAND namespace ============================================================== */

        PyObject* operandDict = xPyDict_New();
        initOperandNamespace(operandDict);
        PyObject* idOperandClass = xPyClass_New(nullptr, operandDict, xPyString_FromString("OPERAND"));

        /* Create the OPTIMIZATION namespace ========================================================= */

        PyObject* modeDict = xPyDict_New();
        initModeNamespace(modeDict);
        PyObject* idModeClass = xPyClass_New(nullptr, modeDict, xPyString_FromString("MODE"));

        /* Create the PE namespace ================================================================== */

        PyObject* peDict = xPyDict_New();
        initPENamespace(peDict);
        PyObject* idPeDictClass = xPyClass_New(nullptr, peDict, xPyString_FromString("PE"));

        /* Create the PREFIX namespace =============================================================== */

        triton::bindings::python::prefixesDict = xPyDict_New();
        PyObject* idPrefixesClass = xPyClass_New(nullptr, triton::bindings::python::prefixesDict, xPyString_FromString("PREFIX"));

        /* Create the REG namespace ================================================================== */

        triton::bindings::python::registersDict = xPyDict_New();
        PyObject* idRegClass = xPyClass_New(nullptr, triton::bindings::python::registersDict, xPyString_FromString("REG"));

        /* Create the SYMEXPR namespace ============================================================== */

        PyObject* symExprDict = xPyDict_New();
        initSymExprNamespace(symExprDict);
        PyObject* idSymExprClass = xPyClass_New(nullptr, symExprDict, xPyString_FromString("SYMEXPR"));

        /* Create the SYSCALL namespace ============================================================== */
        #if defined(__unix__) || defined(__APPLE__)
        triton::bindings::python::syscallsDict = xPyDict_New();
        PyObject* idSyscallsClass = xPyClass_New(nullptr, triton::bindings::python::syscallsDict, xPyString_FromString("SYSCALL"));
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
        PyModule_AddObject(triton::bindings::python::tritonModule, "CPUSIZE",             idCpuSizeClass);            /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "ELF",                 idElfDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "MODE",                idModeClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPCODE",              idOpcodesClass);            /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPERAND",             idOperandClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "PE",                  idPeDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "PREFIX",              idPrefixesClass);           /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "REG",                 idRegClass);                /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYMEXPR",             idSymExprClass);
        #if defined(__unix__) || defined(__APPLE__)
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYSCALL",             idSyscallsClass);           /* Empty: filled on the fly */
        #endif
        PyModule_AddObject(triton::bindings::python::tritonModule, "VERSION",             idVersionClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "ast",                 triton::bindings::python::astModule);

        triton::bindings::python::initialized = true;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

