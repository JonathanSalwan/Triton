//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <iostream>

#include <pythonBindings.hpp>
#include <pythonXFunctions.hpp>
#include <pythonBindings.hpp>



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

        triton::bindings::python::astModule = Py_InitModule("ast", astCallbacks);
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

        /* Create the CPUSIZE namespace ============================================================== */

        triton::bindings::python::cpuSizeDict = xPyDict_New();
        PyObject* idCpuSizeClass = xPyClass_New(nullptr, triton::bindings::python::cpuSizeDict, xPyString_FromString("CPUSIZE"));

        /* Create the OPCODE namespace =============================================================== */

        triton::bindings::python::opcodesDict = xPyDict_New();
        PyObject* idOpcodesClass = xPyClass_New(nullptr, triton::bindings::python::opcodesDict, xPyString_FromString("OPCODE"));

        /* Create the OPERAND namespace ============================================================== */

        PyObject* operandDict = xPyDict_New();
        initOperandNamespace(operandDict);
        PyObject* idOperandClass = xPyClass_New(nullptr, operandDict, xPyString_FromString("OPERAND"));

        /* Create the OPTIMIZATION namespace ========================================================= */

        PyObject* symOptiDict = xPyDict_New();
        initSymOptiNamespace(symOptiDict);
        PyObject* idSymOptiClass = xPyClass_New(nullptr, symOptiDict, xPyString_FromString("OPTIMIZATION"));

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
        PyModule_AddObject(triton::bindings::python::tritonModule, "ast",                 triton::bindings::python::astModule);
        PyModule_AddObject(triton::bindings::python::tritonModule, "ARCH",                idArchDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "AST_NODE",            idAstNodeDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "AST_REPRESENTATION",  idAstRepresentationDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CPUSIZE",             idCpuSizeClass);            /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPCODE",              idOpcodesClass);            /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPERAND",             idOperandClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPTIMIZATION",        idSymOptiClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "PREFIX",              idPrefixesClass);           /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "REG",                 idRegClass);                /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYMEXPR",             idSymExprClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "VERSION",             idVersionClass);
        #if defined(__unix__) || defined(__APPLE__)
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYSCALL",             idSyscallsClass);           /* Empty: filled on the fly */
        #endif

        triton::bindings::python::initialized = true;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */

