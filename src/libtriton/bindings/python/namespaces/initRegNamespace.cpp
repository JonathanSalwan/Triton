//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifdef TRITON_PYTHON_BINDINGS

#include <api.hpp>
#include <architecture.hpp>
#include <pythonBindings.hpp>
#include <pythonObjects.hpp>
#include <x86Specifications.hpp>

#ifdef __unix__
  #include <python2.7/Python.h>
#elif _WIN32
  #include <Python.h>
#endif



/*! \page py_REG_page REG
    \brief [**python api**] All information about the REG python namespace.

\tableofcontents

\section REG_py_description Description
<hr>

According to the CPU architecture, the REG namespace contains all kinds of register.

\section REG_py_api Python API - Items of the REG namespace
<hr>

\subsection REG_X86_py_api x86 registers

- **REG.EAX**
- **REG.AX**
- **REG.AH**
- **REG.AL**
- **REG.EBX**
- **REG.BX**
- **REG.BH**
- **REG.BL**
- **REG.ECX**
- **REG.CX**
- **REG.CH**
- **REG.CL**
- **REG.EDX**
- **REG.DX**
- **REG.DH**
- **REG.DL**
- **REG.EDI**
- **REG.DI**
- **REG.DIL**
- **REG.ESI**
- **REG.SI**
- **REG.SIL**
- **REG.ESP**
- **REG.SP**
- **REG.SPL**
- **REG.EBP**
- **REG.BP**
- **REG.BPL**
- **REG.EIP**
- **REG.IP**
- **REG.EFLAGS**
- **REG.XMM0**
- **REG.XMM1**
- **REG.XMM2**
- **REG.XMM3**
- **REG.XMM4**
- **REG.XMM5**
- **REG.XMM6**
- **REG.XMM7**
- **REG.AF**
- **REG.CF**
- **REG.DF**
- **REG.IF**
- **REG.OF**
- **REG.PF**
- **REG.SF**
- **REG.TF**
- **REG.ZF**

\subsection REG_X8664_py_api x86-64 registers

- **REG.RAX**
- **REG.RBX**
- **REG.RCX**
- **REG.RDX**
- **REG.RDI**
- **REG.RSI**
- **REG.RSP**
- **REG.RBP**
- **REG.RIP**
- **REG.RFLAGS**
- **REG.R8**
- **REG.R8D**
- **REG.R8W**
- **REG.R8B**
- **REG.R9**
- **REG.R9D**
- **REG.R9W**
- **REG.R9B**
- **REG.R10**
- **REG.R10D**
- **REG.R10W**
- **REG.R10B**
- **REG.R11**
- **REG.R11D**
- **REG.R11W**
- **REG.R11B**
- **REG.R12**
- **REG.R12D**
- **REG.R12W**
- **REG.R12B**
- **REG.R13**
- **REG.R13D**
- **REG.R13W**
- **REG.R13B**
- **REG.R14**
- **REG.R14D**
- **REG.R14W**
- **REG.R14B**
- **REG.R15**
- **REG.R15D**
- **REG.R15W**
- **REG.R15B**
- **REG.EAX**
- **REG.AX**
- **REG.AH**
- **REG.AL**
- **REG.EBX**
- **REG.BX**
- **REG.BH**
- **REG.BL**
- **REG.ECX**
- **REG.CX**
- **REG.CH**
- **REG.CL**
- **REG.EDX**
- **REG.DX**
- **REG.DH**
- **REG.DL**
- **REG.EDI**
- **REG.DI**
- **REG.DIL**
- **REG.ESI**
- **REG.SI**
- **REG.SIL**
- **REG.ESP**
- **REG.SP**
- **REG.SPL**
- **REG.EBP**
- **REG.BP**
- **REG.BPL**
- **REG.EIP**
- **REG.IP**
- **REG.XMM0**
- **REG.XMM1**
- **REG.XMM2**
- **REG.XMM3**
- **REG.XMM4**
- **REG.XMM5**
- **REG.XMM6**
- **REG.XMM7**
- **REG.XMM8**
- **REG.XMM9**
- **REG.XMM10**
- **REG.XMM11**
- **REG.XMM12**
- **REG.XMM13**
- **REG.XMM14**
- **REG.XMM15**
- **REG.AF**
- **REG.CF**
- **REG.DF**
- **REG.IF**
- **REG.OF**
- **REG.PF**
- **REG.SF**
- **REG.TF**
- **REG.ZF**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initRegNamespace(void) {

        if (!triton::bindings::python::initialized)
          return;

        switch (api.getArchitecture()) {

          case triton::arch::ARCH_X86_64:
            PyDict_SetItemString(triton::bindings::python::registersDict, "RAX", PyRegisterOperand(TRITON_X86_REG_RAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RBX", PyRegisterOperand(TRITON_X86_REG_RBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RCX", PyRegisterOperand(TRITON_X86_REG_RCX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RDX", PyRegisterOperand(TRITON_X86_REG_RDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RDI", PyRegisterOperand(TRITON_X86_REG_RDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RSI", PyRegisterOperand(TRITON_X86_REG_RSI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RSP", PyRegisterOperand(TRITON_X86_REG_RSP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RBP", PyRegisterOperand(TRITON_X86_REG_RBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RIP", PyRegisterOperand(TRITON_X86_REG_RIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RFLAGS", PyRegisterOperand(TRITON_X86_REG_RFLAGS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8", PyRegisterOperand(TRITON_X86_REG_R8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8D", PyRegisterOperand(TRITON_X86_REG_R8D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8W", PyRegisterOperand(TRITON_X86_REG_R8W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8B", PyRegisterOperand(TRITON_X86_REG_R8B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9", PyRegisterOperand(TRITON_X86_REG_R9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9D", PyRegisterOperand(TRITON_X86_REG_R9D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9W", PyRegisterOperand(TRITON_X86_REG_R9W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9B", PyRegisterOperand(TRITON_X86_REG_R9B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10", PyRegisterOperand(TRITON_X86_REG_R10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10D", PyRegisterOperand(TRITON_X86_REG_R10D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10W", PyRegisterOperand(TRITON_X86_REG_R10W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10B", PyRegisterOperand(TRITON_X86_REG_R10B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11", PyRegisterOperand(TRITON_X86_REG_R11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11D", PyRegisterOperand(TRITON_X86_REG_R11D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11W", PyRegisterOperand(TRITON_X86_REG_R11W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11B", PyRegisterOperand(TRITON_X86_REG_R11B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12", PyRegisterOperand(TRITON_X86_REG_R12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12D", PyRegisterOperand(TRITON_X86_REG_R12D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12W", PyRegisterOperand(TRITON_X86_REG_R12W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12B", PyRegisterOperand(TRITON_X86_REG_R12B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13", PyRegisterOperand(TRITON_X86_REG_R13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13D", PyRegisterOperand(TRITON_X86_REG_R13D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13W", PyRegisterOperand(TRITON_X86_REG_R13W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13B", PyRegisterOperand(TRITON_X86_REG_R13B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14", PyRegisterOperand(TRITON_X86_REG_R14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14D", PyRegisterOperand(TRITON_X86_REG_R14D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14W", PyRegisterOperand(TRITON_X86_REG_R14W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14B", PyRegisterOperand(TRITON_X86_REG_R14B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15", PyRegisterOperand(TRITON_X86_REG_R15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15D", PyRegisterOperand(TRITON_X86_REG_R15D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15W", PyRegisterOperand(TRITON_X86_REG_R15W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15B", PyRegisterOperand(TRITON_X86_REG_R15B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM8", PyRegisterOperand(TRITON_X86_REG_XMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM9", PyRegisterOperand(TRITON_X86_REG_XMM9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM10", PyRegisterOperand(TRITON_X86_REG_XMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM11", PyRegisterOperand(TRITON_X86_REG_XMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM12", PyRegisterOperand(TRITON_X86_REG_XMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM13", PyRegisterOperand(TRITON_X86_REG_XMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM14", PyRegisterOperand(TRITON_X86_REG_XMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM15", PyRegisterOperand(TRITON_X86_REG_XMM15));

          case triton::arch::ARCH_X86:
            PyDict_SetItemString(triton::bindings::python::registersDict, "EAX", PyRegisterOperand(TRITON_X86_REG_EAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AX", PyRegisterOperand(TRITON_X86_REG_AX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AH", PyRegisterOperand(TRITON_X86_REG_AH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AL", PyRegisterOperand(TRITON_X86_REG_AL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBX", PyRegisterOperand(TRITON_X86_REG_EBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BX", PyRegisterOperand(TRITON_X86_REG_BX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BH", PyRegisterOperand(TRITON_X86_REG_BH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BL", PyRegisterOperand(TRITON_X86_REG_BL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ECX", PyRegisterOperand(TRITON_X86_REG_ECX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CX", PyRegisterOperand(TRITON_X86_REG_CX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CH", PyRegisterOperand(TRITON_X86_REG_CH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CL", PyRegisterOperand(TRITON_X86_REG_CL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDX", PyRegisterOperand(TRITON_X86_REG_EDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DX", PyRegisterOperand(TRITON_X86_REG_DX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DH", PyRegisterOperand(TRITON_X86_REG_DH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DL", PyRegisterOperand(TRITON_X86_REG_DL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDI", PyRegisterOperand(TRITON_X86_REG_EDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DI", PyRegisterOperand(TRITON_X86_REG_DI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DIL", PyRegisterOperand(TRITON_X86_REG_DIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESI", PyRegisterOperand(TRITON_X86_REG_ESI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SI", PyRegisterOperand(TRITON_X86_REG_SI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SIL", PyRegisterOperand(TRITON_X86_REG_SIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESP", PyRegisterOperand(TRITON_X86_REG_ESP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SP", PyRegisterOperand(TRITON_X86_REG_SP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SPL", PyRegisterOperand(TRITON_X86_REG_SPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBP", PyRegisterOperand(TRITON_X86_REG_EBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BP", PyRegisterOperand(TRITON_X86_REG_BP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BPL", PyRegisterOperand(TRITON_X86_REG_BPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EIP", PyRegisterOperand(TRITON_X86_REG_EIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IP", PyRegisterOperand(TRITON_X86_REG_IP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EFLAGS", PyRegisterOperand(TRITON_X86_REG_EFLAGS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM0", PyRegisterOperand(TRITON_X86_REG_XMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM1", PyRegisterOperand(TRITON_X86_REG_XMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM2", PyRegisterOperand(TRITON_X86_REG_XMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM3", PyRegisterOperand(TRITON_X86_REG_XMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM4", PyRegisterOperand(TRITON_X86_REG_XMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM5", PyRegisterOperand(TRITON_X86_REG_XMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM6", PyRegisterOperand(TRITON_X86_REG_XMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM7", PyRegisterOperand(TRITON_X86_REG_XMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AF", PyRegisterOperand(TRITON_X86_REG_AF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CF", PyRegisterOperand(TRITON_X86_REG_CF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DF", PyRegisterOperand(TRITON_X86_REG_DF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IF", PyRegisterOperand(TRITON_X86_REG_IF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OF", PyRegisterOperand(TRITON_X86_REG_OF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PF", PyRegisterOperand(TRITON_X86_REG_PF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SF", PyRegisterOperand(TRITON_X86_REG_SF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "TF", PyRegisterOperand(TRITON_X86_REG_TF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZF", PyRegisterOperand(TRITON_X86_REG_ZF));
            break;
        } /* switch */

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
