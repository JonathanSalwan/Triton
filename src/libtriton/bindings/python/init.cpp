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

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



namespace triton {
  namespace bindings {
    namespace python {

      /* Triton module */
      bool      initialized           = false;
      PyObject* cpuSizeDict           = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* opcodesDict           = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* registersDict         = nullptr; /* Must be global because it's updated on-the-fly */
      PyObject* smt2libModule         = nullptr; /* Must be global because may be updated on-the-fly */
      PyObject* tritonModule          = nullptr; /* Must be global because may be updated on-the-fly */
      #ifdef __unix__
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

        /* Create the smt2lib module ================================================================= */

        triton::bindings::python::smt2libModule = Py_InitModule("smt2lib", smt2libCallbacks);
        if (triton::bindings::python::smt2libModule == nullptr) {
          std::cerr << "Failed to initialize the smt2lib bindings" << std::endl;
          PyErr_Print();
          exit(1);
        }


        /* Create the ARCH namespace ========================================================= */

        PyObject* archDict = xPyDict_New();
        initArchNamespace(archDict);
        PyObject* idArchDictClass = xPyClass_New(nullptr, archDict, xPyString_FromString("ARCH"));

        /* Create the CPUSIZE namespace ============================================================== */

        triton::bindings::python::cpuSizeDict = xPyDict_New();
        PyObject* idCpuSizeClass = xPyClass_New(nullptr, triton::bindings::python::cpuSizeDict, xPyString_FromString("CPUSIZE"));

        /* Create the OPCODE namespace ============================================================== */

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

        /* Create the REG namespace ================================================================== */

        triton::bindings::python::registersDict = xPyDict_New();
        PyObject* idRegClass = xPyClass_New(nullptr, triton::bindings::python::registersDict, xPyString_FromString("REG"));

        /* Create the SMT_AST_NODE namespace ========================================================= */

        PyObject* smtAstNodeDict = xPyDict_New();
        initSmtAstNodeNamespace(smtAstNodeDict);
        PyObject* idSmtAstNodeDictClass = xPyClass_New(nullptr, smtAstNodeDict, xPyString_FromString("SMT_AST_NODE"));

        /* Create the SYMEXPR namespace ============================================================== */

        PyObject* symExprDict = xPyDict_New();
        initSymExprNamespace(symExprDict);
        PyObject* idSymExprClass = xPyClass_New(nullptr, symExprDict, xPyString_FromString("SYMEXPR"));

        /* Create the SYSCALL namespace ============================================================== */
        #ifdef __unix__
        triton::bindings::python::syscallsDict = xPyDict_New();
        PyObject* idSyscallsClass = xPyClass_New(nullptr, triton::bindings::python::syscallsDict, xPyString_FromString("SYSCALL"));
        #endif

        /* Create the VERSION namespace ============================================================== */

        PyObject* versionDict = xPyDict_New();
        initVersionNamespace(versionDict);
        PyObject* idVersionClass = xPyClass_New(nullptr, versionDict, xPyString_FromString("VERSION"));


        /* Init triton module ======================================================================== */

        /* Add every modules and namespace into the triton module */
        PyModule_AddObject(triton::bindings::python::tritonModule, "ARCH",              idArchDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CPUSIZE",           idCpuSizeClass);            /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPCODE",            idOpcodesClass);            /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPERAND",           idOperandClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPTIMIZATION",      idSymOptiClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "REG",               idRegClass);                /* Empty: filled on the fly */
        PyModule_AddObject(triton::bindings::python::tritonModule, "SMT_AST_NODE",      idSmtAstNodeDictClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYMEXPR",           idSymExprClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "VERSION",           idVersionClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "smt2lib",           triton::bindings::python::smt2libModule);
        #ifdef __unix__
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYSCALL",           idSyscallsClass);           /* Empty: filled on the fly */
        #endif

        triton::bindings::python::initialized = true;

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */

