//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <map>
#include <vector>

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

- <b>STUBS.AARCH64.LIBC.code</b><br>
The libc stub on AArch64 architecture with the ARM64 ABI calling convention.

- <b>STUBS.AARCH64.LIBC.symbols</b><br>
The symbols map of the AArch64 libc stub.

- <b>STUBS.I386.SYSTEMV.LIBC.code</b><br>
The libc stub on i386 architecture with the SystemV ABI calling convention.

- <b>STUBS.I386.SYSTEMV.LIBC.symbols</b><br>
The symbols map of the i386-systemv libc stub.

- <b>STUBS.X8664.MS.LIBC.code</b><br>
The libc stub on x8664 architecture with the MS ABI calling convention.

- <b>STUBS.X8664.MS.LIBC.symbols</b><br>
The symbols map of the x8664-ms libc stub.

- <b>STUBS.X8664.SYSTEMV.LIBC.code</b><br>
The libc stub on x8664 architecture with the SystemV ABI calling convention.

- <b>STUBS.X8664.SYSTEMV.LIBC.symbols</b><br>
The symbols map of the x8664-systemv libc stub.

*/



namespace triton {
  namespace bindings {
    namespace python {

      static PyObject* initCode(const std::vector<triton::uint8>& code) {
        auto* area = new triton::uint8[code.size()];

        for (triton::usize index = 0; index < code.size(); index++)
          area[index] = code[index];

        auto* ret = PyBytes_FromStringAndSize(reinterpret_cast<const char*>(area), code.size());
        delete[] area;

        return ret;
      }


      static PyObject* initSymbols(const std::map<std::string, triton::uint64>& symbols) {
        PyObject* symbolsDict = xPyDict_New();
        for (const auto& it : symbols) {
          xPyDict_SetItem(symbolsDict, xPyString_FromString(it.first.c_str()), PyLong_FromUsize(it.second));
        }
        return symbolsDict;
      }


      static PyObject* initLibc(const std::vector<triton::uint8>& code, const std::map<std::string, triton::uint64>& symbols) {
        PyObject* libcDict = xPyDict_New();
        xPyDict_SetItemString(libcDict, "code", initCode(code));
        xPyDict_SetItemString(libcDict, "symbols", initSymbols(symbols));
        PyObject* libcDictClass = xPyClass_New(nullptr, libcDict, xPyString_FromString("LIBC"));

        return libcDictClass;
      }


      static PyObject* initSystemV(const std::vector<triton::uint8>& code, const std::map<std::string, triton::uint64>& symbols) {
        PyObject* systemvDict = xPyDict_New();
        xPyDict_SetItemString(systemvDict, "LIBC", initLibc(code, symbols));
        PyObject* systemvDictClass = xPyClass_New(nullptr, systemvDict, xPyString_FromString("SYSTEMV"));
        return systemvDictClass;
      }


      static PyObject* initMS(const std::vector<triton::uint8>& code, const std::map<std::string, triton::uint64>& symbols) {
        PyObject* systemvDict = xPyDict_New();
        xPyDict_SetItemString(systemvDict, "LIBC", initLibc(code, symbols));
        PyObject* systemvDictClass = xPyClass_New(nullptr, systemvDict, xPyString_FromString("MS"));
        return systemvDictClass;
      }


      static PyObject* initX8664(void) {
        PyObject* dict = xPyDict_New();
        xPyDict_SetItemString(dict, "SYSTEMV", initSystemV(triton::stubs::x8664::systemv::libc::code, triton::stubs::x8664::systemv::libc::symbols));
        xPyDict_SetItemString(dict, "MS", initMS(triton::stubs::x8664::ms::libc::code, triton::stubs::x8664::ms::libc::symbols));
        PyObject* dictClass = xPyClass_New(nullptr, dict, xPyString_FromString("X8664"));
        return dictClass;
      }


      static PyObject* initAArch64(void) {
        PyObject* dict = xPyDict_New();
        xPyDict_SetItemString(dict, "LIBC", initLibc(triton::stubs::aarch64::libc::code, triton::stubs::aarch64::libc::symbols));
        PyObject* dictClass = xPyClass_New(nullptr, dict, xPyString_FromString("AARCH64"));
        return dictClass;
      }


      static PyObject* initI386(void) {
        PyObject* dict = xPyDict_New();
        xPyDict_SetItemString(dict, "SYSTEMV", initSystemV(triton::stubs::i386::systemv::libc::code, triton::stubs::i386::systemv::libc::symbols));
        PyObject* dictClass = xPyClass_New(nullptr, dict, xPyString_FromString("I386"));
        return dictClass;
      }


      void initStubsNamespace(PyObject* stubsDict) {
        xPyDict_SetItemString(stubsDict, "AARCH64", initAArch64());
        xPyDict_SetItemString(stubsDict, "I386",    initI386());
        xPyDict_SetItemString(stubsDict, "X8664",   initX8664());
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
