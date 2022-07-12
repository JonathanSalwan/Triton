//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
#include <triton/stubs.hpp>



/*! \page py_STUBS_page STUBS
    \brief [**python api**] All information about the STUBS Python namespace.

\tableofcontents

\section STUBS_py_description Description
<hr>

The STUBS namespace contains all stubs.

\section STUBS_py_api Python API - Items of the STUBS namespace
<hr>

- <b>STUBS.X8664.SYSTEMV.LIBC.code</b><br>
The libc stub on x8664 architecture with the SystemV ABI calling convention.

- <b>STUBS.X8664.SYSTEMV.LIBC.symbols</b><br>
The symbols map of the libc stub.

*/



namespace triton {
  namespace bindings {
    namespace python {

      static PyObject* initCode(void) {
        auto vv = triton::stubs::x8664::systemv::libc::code;
        auto* area = new triton::uint8[vv.size()];

        for (triton::usize index = 0; index < vv.size(); index++)
          area[index] = vv[index];

        auto* code = PyBytes_FromStringAndSize(reinterpret_cast<const char*>(area), vv.size());
        delete[] area;

        return code;
      }

      static PyObject* initSymbols(void) {
        PyObject* symbolsDict = xPyDict_New();
        for (const auto& it : triton::stubs::x8664::systemv::libc::symbols) {
          xPyDict_SetItem(symbolsDict, xPyString_FromString(it.first.c_str()), PyLong_FromUsize(it.second));
        }
        return symbolsDict;
      }

      static PyObject* initLibc(void) {
        PyObject* libcDict = xPyDict_New();
        xPyDict_SetItemString(libcDict, "code", initCode());
        xPyDict_SetItemString(libcDict, "symbols", initSymbols());
        PyObject* libcDictClass = xPyClass_New(nullptr, libcDict, xPyString_FromString("LIBC"));

        return libcDictClass;
      }

      static PyObject* initSystemV(void) {
        PyObject* systemvDict = xPyDict_New();
        xPyDict_SetItemString(systemvDict, "LIBC", initLibc());
        PyObject* systemvDictClass = xPyClass_New(nullptr, systemvDict, xPyString_FromString("SYSTEMV"));
        return systemvDictClass;
      }

      static PyObject* initx8664(void) {
        PyObject* x8664Dict = xPyDict_New();
        xPyDict_SetItemString(x8664Dict, "SYSTEMV", initSystemV());
        PyObject* x8664DictClass = xPyClass_New(nullptr, x8664Dict, xPyString_FromString("X8664"));
        return x8664DictClass;
      }

      void initStubsNamespace(PyObject* stubsDict) {
        xPyDict_SetItemString(stubsDict, "X8664", initx8664());
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
