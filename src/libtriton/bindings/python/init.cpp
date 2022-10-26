//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonXFunctions.hpp>

#include <iostream>



namespace triton {
  namespace bindings {
    namespace python {

      /* Triton module */
      PyObject* tritonModule = nullptr; /* Must be global because may be updated on-the-fly */

      PyModuleDef tritonModuleDef = {
        PyModuleDef_HEAD_INIT,
        "triton",
        NULL,
        -1,
        #if IS_PY3
        tritonCallbacks,
        NULL, /* m_slots    */
        NULL, /* m_traverse */
        NULL, /* m_clear    */
        NULL  /* m_free     */
        #else
        tritonCallbacks
        #endif
      };

      /* Python entry point (Py2/3) */
      #if IS_PY3
      PyMODINIT_FUNC PyInit_triton(void) {
      #else
      PyMODINIT_FUNC inittriton(void) {
        PyInit_triton();
      }
      PyObject* PyInit_triton(void) {
      #endif
        /* Init python */
        Py_Initialize();

        /* Create the triton module ================================================================== */

        triton::bindings::python::tritonModule = PyModule_Create(&tritonModuleDef);
        if (triton::bindings::python::tritonModule == nullptr) {
          std::cerr << "Failed to initialize the triton bindings" << std::endl;
          PyErr_Print();
          return nullptr;
        }

        /* Create the ARCH namespace ================================================================= */

        PyObject* archDict = xPyDict_New();
        initArchNamespace(archDict);
        PyObject* idArchClass = xPyClass_New(nullptr, archDict, xPyString_FromString("ARCH"));

        /* Create the AST_NODE namespace ============================================================= */

        PyObject* astNodeDict = xPyDict_New();
        initAstNodeNamespace(astNodeDict);
        PyObject* idAstNodeClass = xPyClass_New(nullptr, astNodeDict, xPyString_FromString("AST_NODE"));

        /* Create the AST_REPRESENTATION namespace =================================================== */

        PyObject* astRepresentationDict = xPyDict_New();
        initAstRepresentationNamespace(astRepresentationDict);
        PyObject* idAstRepresentationClass = xPyClass_New(nullptr, astRepresentationDict, xPyString_FromString("AST_REPRESENTATION"));

        /* Create the CALLBACK namespace ============================================================= */

        PyObject* callbackDict = xPyDict_New();
        initCallbackNamespace(callbackDict);
        PyObject* idCallbackClass = xPyClass_New(nullptr, callbackDict, xPyString_FromString("CALLBACK"));

        /* Create the CONDITION namespace ============================================================ */

        PyObject* conditionsDict = xPyDict_New();
        initConditionsNamespace(conditionsDict);
        PyObject* idConditionsClass = xPyClass_New(nullptr, conditionsDict, xPyString_FromString("CONDITION"));

        /* Create the CPUSIZE namespace ============================================================== */

        PyObject* cpuSizeDict = xPyDict_New();
        initCpuSizeNamespace(cpuSizeDict);
        PyObject* idCpuSizeClass = xPyClass_New(nullptr, cpuSizeDict, xPyString_FromString("CPUSIZE"));

        /* Create the EXCEPTION namespace ============================================================ */

        PyObject* exceptionDict = xPyDict_New();
        initExceptionNamespace(exceptionDict);
        PyObject* idExceptionClass = xPyClass_New(nullptr, exceptionDict, xPyString_FromString("EXCEPTION"));

        /* Create the EXTEND namespace =============================================================== */

        PyObject* extendDict = xPyDict_New();
        initExtendNamespace(extendDict);
        PyObject* idExtendClass = xPyClass_New(nullptr, extendDict, xPyString_FromString("EXTEND"));

        /* Create the VAS namespace ================================================================== */

        PyObject* vasDict = xPyDict_New();
        initVASNamespace(vasDict);
        PyObject* idVASClass = xPyClass_New(nullptr, vasDict, xPyString_FromString("VAS"));

        /* Create the OPCODE namespace =============================================================== */

        PyObject* opcodesDict = xPyDict_New();
        initOpcodesNamespace(opcodesDict);
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
        initPrefixesNamespace(prefixesDict);
        PyObject* idPrefixesClass = xPyClass_New(nullptr, prefixesDict, xPyString_FromString("PREFIX"));

        /* Create the REG namespace ================================================================== */

        PyObject* registersDict = xPyDict_New();
        initRegNamespace(registersDict);
        PyObject* idRegClass = xPyClass_New(nullptr, registersDict, xPyString_FromString("REG"));

        /* Create the SHIFT namespace ================================================================ */

        PyObject* shiftsDict = xPyDict_New();
        initShiftsNamespace(shiftsDict);
        PyObject* idShiftsClass = xPyClass_New(nullptr, shiftsDict, xPyString_FromString("SHIFT"));

        /* Create the SOLVER namespace =============================================================== */

        PyObject* solverDict = xPyDict_New();
        initSolverNamespace(solverDict);
        PyObject* idSolverClass = xPyClass_New(nullptr, solverDict, xPyString_FromString("SOLVER"));

        /* Create the SOLVER_STATE namespace ========================================================= */

        PyObject* solverStateDict = xPyDict_New();
        initSolverStateNamespace(solverStateDict);
        PyObject* idSolverStateClass = xPyClass_New(nullptr, solverStateDict, xPyString_FromString("SOLVER_STATE"));

        /* Create the STUBS namespace ============================================================= */

        PyObject* stubsDict = xPyDict_New();
        initStubsNamespace(stubsDict);
        PyObject* idStubsClass = xPyClass_New(nullptr, stubsDict, xPyString_FromString("STUBS"));

        /* Create the SYMBOLIC namespace ============================================================= */

        PyObject* symbolicDict = xPyDict_New();
        initSymbolicNamespace(symbolicDict);
        PyObject* idSymbolicClass = xPyClass_New(nullptr, symbolicDict, xPyString_FromString("SYMBOLIC"));

        /* Create the VERSION namespace ============================================================== */

        PyObject* versionDict = xPyDict_New();
        initVersionNamespace(versionDict);
        PyObject* idVersionClass = xPyClass_New(nullptr, versionDict, xPyString_FromString("VERSION"));


        /* Init triton module ======================================================================== */

        /* Add every modules and namespace into the triton module */
        PyModule_AddObject(triton::bindings::python::tritonModule, "ARCH",                idArchClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "AST_NODE",            idAstNodeClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "AST_REPRESENTATION",  idAstRepresentationClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CALLBACK",            idCallbackClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CONDITION",           idConditionsClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "CPUSIZE",             idCpuSizeClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "EXCEPTION",           idExceptionClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "EXTEND",              idExtendClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "MODE",                idModeClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPCODE",              idOpcodesClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "OPERAND",             idOperandClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "PREFIX",              idPrefixesClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "REG",                 idRegClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "SHIFT",               idShiftsClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "SOLVER",              idSolverClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "SOLVER_STATE",        idSolverStateClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "STUBS",               idStubsClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "SYMBOLIC",            idSymbolicClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "VAS",                 idVASClass);
        PyModule_AddObject(triton::bindings::python::tritonModule, "VERSION",             idVersionClass);

        return triton::bindings::python::tritonModule;
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

