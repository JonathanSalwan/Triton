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
- **REG.MM0**
- **REG.MM1**
- **REG.MM2**
- **REG.MM3**
- **REG.MM4**
- **REG.MM5**
- **REG.MM6**
- **REG.MM7**
- **REG.XMM0**
- **REG.XMM1**
- **REG.XMM2**
- **REG.XMM3**
- **REG.XMM4**
- **REG.XMM5**
- **REG.XMM6**
- **REG.XMM7**
- **REG.YMM0**
- **REG.YMM1**
- **REG.YMM2**
- **REG.YMM3**
- **REG.YMM4**
- **REG.YMM5**
- **REG.YMM6**
- **REG.YMM7**
- **REG.MXCSR**
- **REG.CR0**
- **REG.CR1**
- **REG.CR2**
- **REG.CR3**
- **REG.CR4**
- **REG.CR5**
- **REG.CR6**
- **REG.CR7**
- **REG.CR8**
- **REG.CR9**
- **REG.CR10**
- **REG.CR11**
- **REG.CR12**
- **REG.CR13**
- **REG.CR14**
- **REG.CR15**
- **REG.IE**
- **REG.DE**
- **REG.ZE**
- **REG.OE**
- **REG.UE**
- **REG.PE**
- **REG.DAZ**
- **REG.IM**
- **REG.DM**
- **REG.ZM**
- **REG.OM**
- **REG.UM**
- **REG.PM**
- **REG.RL**
- **REG.RH**
- **REG.FZ**
- **REG.AF**
- **REG.CF**
- **REG.DF**
- **REG.IF**
- **REG.OF**
- **REG.PF**
- **REG.SF**
- **REG.TF**
- **REG.ZF**
- **REG.CS**
- **REG.DS**
- **REG.ES**
- **REG.FS**
- **REG.GS**
- **REG.SS**

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
- **REG.EFLAGS**
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
- **REG.MM0**
- **REG.MM1**
- **REG.MM2**
- **REG.MM3**
- **REG.MM4**
- **REG.MM5**
- **REG.MM6**
- **REG.MM7**
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
- **REG.YMM0**
- **REG.YMM1**
- **REG.YMM2**
- **REG.YMM3**
- **REG.YMM4**
- **REG.YMM5**
- **REG.YMM6**
- **REG.YMM7**
- **REG.YMM8**
- **REG.YMM9**
- **REG.YMM10**
- **REG.YMM11**
- **REG.YMM12**
- **REG.YMM13**
- **REG.YMM14**
- **REG.YMM15**
- **REG.ZMM0**
- **REG.ZMM1**
- **REG.ZMM2**
- **REG.ZMM3**
- **REG.ZMM4**
- **REG.ZMM5**
- **REG.ZMM6**
- **REG.ZMM7**
- **REG.ZMM8**
- **REG.ZMM9**
- **REG.ZMM10**
- **REG.ZMM11**
- **REG.ZMM12**
- **REG.ZMM13**
- **REG.ZMM14**
- **REG.ZMM15**
- **REG.ZMM16**
- **REG.ZMM17**
- **REG.ZMM18**
- **REG.ZMM19**
- **REG.ZMM20**
- **REG.ZMM21**
- **REG.ZMM22**
- **REG.ZMM23**
- **REG.ZMM24**
- **REG.ZMM25**
- **REG.ZMM26**
- **REG.ZMM27**
- **REG.ZMM28**
- **REG.ZMM29**
- **REG.ZMM30**
- **REG.ZMM31**
- **REG.MXCSR**
- **REG.CR0**
- **REG.CR1**
- **REG.CR2**
- **REG.CR3**
- **REG.CR4**
- **REG.CR5**
- **REG.CR6**
- **REG.CR7**
- **REG.CR8**
- **REG.CR9**
- **REG.CR10**
- **REG.CR11**
- **REG.CR12**
- **REG.CR13**
- **REG.CR14**
- **REG.CR15**
- **REG.IE**
- **REG.DE**
- **REG.ZE**
- **REG.OE**
- **REG.UE**
- **REG.PE**
- **REG.DAZ**
- **REG.IM**
- **REG.DM**
- **REG.ZM**
- **REG.OM**
- **REG.UM**
- **REG.PM**
- **REG.RL**
- **REG.RH**
- **REG.FZ**
- **REG.AF**
- **REG.CF**
- **REG.DF**
- **REG.IF**
- **REG.OF**
- **REG.PF**
- **REG.SF**
- **REG.TF**
- **REG.ZF**
- **REG.CS**
- **REG.DS**
- **REG.ES**
- **REG.FS**
- **REG.GS**
- **REG.SS**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initRegNamespace(void) {
        if (!triton::bindings::python::initialized)
          return;

        PyDict_Clear(triton::bindings::python::registersDict);

        switch (api.getArchitecture()) {
          case triton::arch::ARCH_X86_64:
            PyDict_SetItemString(triton::bindings::python::registersDict, "AF",     PyRegisterOperand(TRITON_X86_REG_AF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AH",     PyRegisterOperand(TRITON_X86_REG_AH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AL",     PyRegisterOperand(TRITON_X86_REG_AL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AX",     PyRegisterOperand(TRITON_X86_REG_AX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BH",     PyRegisterOperand(TRITON_X86_REG_BH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BL",     PyRegisterOperand(TRITON_X86_REG_BL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BP",     PyRegisterOperand(TRITON_X86_REG_BP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BPL",    PyRegisterOperand(TRITON_X86_REG_BPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BX",     PyRegisterOperand(TRITON_X86_REG_BX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CF",     PyRegisterOperand(TRITON_X86_REG_CF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CH",     PyRegisterOperand(TRITON_X86_REG_CH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CL",     PyRegisterOperand(TRITON_X86_REG_CL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR0",    PyRegisterOperand(TRITON_X86_REG_CR0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR1",    PyRegisterOperand(TRITON_X86_REG_CR1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR10",   PyRegisterOperand(TRITON_X86_REG_CR10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR11",   PyRegisterOperand(TRITON_X86_REG_CR11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR12",   PyRegisterOperand(TRITON_X86_REG_CR12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR13",   PyRegisterOperand(TRITON_X86_REG_CR13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR14",   PyRegisterOperand(TRITON_X86_REG_CR14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR15",   PyRegisterOperand(TRITON_X86_REG_CR15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR2",    PyRegisterOperand(TRITON_X86_REG_CR2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR3",    PyRegisterOperand(TRITON_X86_REG_CR3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR4",    PyRegisterOperand(TRITON_X86_REG_CR4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR5",    PyRegisterOperand(TRITON_X86_REG_CR5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR6",    PyRegisterOperand(TRITON_X86_REG_CR6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR7",    PyRegisterOperand(TRITON_X86_REG_CR7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR8",    PyRegisterOperand(TRITON_X86_REG_CR8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR9",    PyRegisterOperand(TRITON_X86_REG_CR9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CS",     PyRegisterOperand(TRITON_X86_REG_CS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CX",     PyRegisterOperand(TRITON_X86_REG_CX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DAZ",    PyRegisterOperand(TRITON_X86_REG_DAZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DE",     PyRegisterOperand(TRITON_X86_REG_DE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DF",     PyRegisterOperand(TRITON_X86_REG_DF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DH",     PyRegisterOperand(TRITON_X86_REG_DH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DI",     PyRegisterOperand(TRITON_X86_REG_DI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DIL",    PyRegisterOperand(TRITON_X86_REG_DIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DL",     PyRegisterOperand(TRITON_X86_REG_DL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DM",     PyRegisterOperand(TRITON_X86_REG_DM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DS",     PyRegisterOperand(TRITON_X86_REG_DS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DX",     PyRegisterOperand(TRITON_X86_REG_DX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EAX",    PyRegisterOperand(TRITON_X86_REG_EAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBP",    PyRegisterOperand(TRITON_X86_REG_EBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBX",    PyRegisterOperand(TRITON_X86_REG_EBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ECX",    PyRegisterOperand(TRITON_X86_REG_ECX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDI",    PyRegisterOperand(TRITON_X86_REG_EDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDX",    PyRegisterOperand(TRITON_X86_REG_EDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EFLAGS", PyRegisterOperand(TRITON_X86_REG_EFLAGS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EIP",    PyRegisterOperand(TRITON_X86_REG_EIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ES",     PyRegisterOperand(TRITON_X86_REG_ES));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESI",    PyRegisterOperand(TRITON_X86_REG_ESI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESP",    PyRegisterOperand(TRITON_X86_REG_ESP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FS",     PyRegisterOperand(TRITON_X86_REG_FS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FZ",     PyRegisterOperand(TRITON_X86_REG_FZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "GS",     PyRegisterOperand(TRITON_X86_REG_GS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IE",     PyRegisterOperand(TRITON_X86_REG_IE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IF",     PyRegisterOperand(TRITON_X86_REG_IF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IM",     PyRegisterOperand(TRITON_X86_REG_IM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IP",     PyRegisterOperand(TRITON_X86_REG_IP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM0",    PyRegisterOperand(TRITON_X86_REG_MM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM1",    PyRegisterOperand(TRITON_X86_REG_MM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM2",    PyRegisterOperand(TRITON_X86_REG_MM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM3",    PyRegisterOperand(TRITON_X86_REG_MM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM4",    PyRegisterOperand(TRITON_X86_REG_MM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM5",    PyRegisterOperand(TRITON_X86_REG_MM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM6",    PyRegisterOperand(TRITON_X86_REG_MM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM7",    PyRegisterOperand(TRITON_X86_REG_MM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MXCSR",  PyRegisterOperand(TRITON_X86_REG_MXCSR));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OE",     PyRegisterOperand(TRITON_X86_REG_OE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OF",     PyRegisterOperand(TRITON_X86_REG_OF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OM",     PyRegisterOperand(TRITON_X86_REG_OM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PE",     PyRegisterOperand(TRITON_X86_REG_PE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PF",     PyRegisterOperand(TRITON_X86_REG_PF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PM",     PyRegisterOperand(TRITON_X86_REG_PM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10",    PyRegisterOperand(TRITON_X86_REG_R10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10B",   PyRegisterOperand(TRITON_X86_REG_R10B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10D",   PyRegisterOperand(TRITON_X86_REG_R10D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10W",   PyRegisterOperand(TRITON_X86_REG_R10W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11",    PyRegisterOperand(TRITON_X86_REG_R11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11B",   PyRegisterOperand(TRITON_X86_REG_R11B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11D",   PyRegisterOperand(TRITON_X86_REG_R11D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11W",   PyRegisterOperand(TRITON_X86_REG_R11W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12",    PyRegisterOperand(TRITON_X86_REG_R12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12B",   PyRegisterOperand(TRITON_X86_REG_R12B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12D",   PyRegisterOperand(TRITON_X86_REG_R12D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12W",   PyRegisterOperand(TRITON_X86_REG_R12W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13",    PyRegisterOperand(TRITON_X86_REG_R13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13B",   PyRegisterOperand(TRITON_X86_REG_R13B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13D",   PyRegisterOperand(TRITON_X86_REG_R13D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13W",   PyRegisterOperand(TRITON_X86_REG_R13W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14",    PyRegisterOperand(TRITON_X86_REG_R14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14B",   PyRegisterOperand(TRITON_X86_REG_R14B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14D",   PyRegisterOperand(TRITON_X86_REG_R14D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14W",   PyRegisterOperand(TRITON_X86_REG_R14W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15",    PyRegisterOperand(TRITON_X86_REG_R15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15B",   PyRegisterOperand(TRITON_X86_REG_R15B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15D",   PyRegisterOperand(TRITON_X86_REG_R15D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15W",   PyRegisterOperand(TRITON_X86_REG_R15W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8",     PyRegisterOperand(TRITON_X86_REG_R8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8B",    PyRegisterOperand(TRITON_X86_REG_R8B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8D",    PyRegisterOperand(TRITON_X86_REG_R8D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8W",    PyRegisterOperand(TRITON_X86_REG_R8W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9",     PyRegisterOperand(TRITON_X86_REG_R9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9B",    PyRegisterOperand(TRITON_X86_REG_R9B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9D",    PyRegisterOperand(TRITON_X86_REG_R9D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9W",    PyRegisterOperand(TRITON_X86_REG_R9W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RAX",    PyRegisterOperand(TRITON_X86_REG_RAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RBP",    PyRegisterOperand(TRITON_X86_REG_RBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RBX",    PyRegisterOperand(TRITON_X86_REG_RBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RCX",    PyRegisterOperand(TRITON_X86_REG_RCX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RDI",    PyRegisterOperand(TRITON_X86_REG_RDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RDX",    PyRegisterOperand(TRITON_X86_REG_RDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RH",     PyRegisterOperand(TRITON_X86_REG_RH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RIP",    PyRegisterOperand(TRITON_X86_REG_RIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RL",     PyRegisterOperand(TRITON_X86_REG_RL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RSI",    PyRegisterOperand(TRITON_X86_REG_RSI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RSP",    PyRegisterOperand(TRITON_X86_REG_RSP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SF",     PyRegisterOperand(TRITON_X86_REG_SF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SI",     PyRegisterOperand(TRITON_X86_REG_SI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SIL",    PyRegisterOperand(TRITON_X86_REG_SIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SP",     PyRegisterOperand(TRITON_X86_REG_SP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SPL",    PyRegisterOperand(TRITON_X86_REG_SPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SS",     PyRegisterOperand(TRITON_X86_REG_SS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "TF",     PyRegisterOperand(TRITON_X86_REG_TF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UE",     PyRegisterOperand(TRITON_X86_REG_UE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UM",     PyRegisterOperand(TRITON_X86_REG_UM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM0",   PyRegisterOperand(TRITON_X86_REG_XMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM1",   PyRegisterOperand(TRITON_X86_REG_XMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM10",  PyRegisterOperand(TRITON_X86_REG_XMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM11",  PyRegisterOperand(TRITON_X86_REG_XMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM12",  PyRegisterOperand(TRITON_X86_REG_XMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM13",  PyRegisterOperand(TRITON_X86_REG_XMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM14",  PyRegisterOperand(TRITON_X86_REG_XMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM15",  PyRegisterOperand(TRITON_X86_REG_XMM15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM2",   PyRegisterOperand(TRITON_X86_REG_XMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM3",   PyRegisterOperand(TRITON_X86_REG_XMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM4",   PyRegisterOperand(TRITON_X86_REG_XMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM5",   PyRegisterOperand(TRITON_X86_REG_XMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM6",   PyRegisterOperand(TRITON_X86_REG_XMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM7",   PyRegisterOperand(TRITON_X86_REG_XMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM8",   PyRegisterOperand(TRITON_X86_REG_XMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM9",   PyRegisterOperand(TRITON_X86_REG_XMM9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM0",   PyRegisterOperand(TRITON_X86_REG_YMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM1",   PyRegisterOperand(TRITON_X86_REG_YMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM10",  PyRegisterOperand(TRITON_X86_REG_YMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM11",  PyRegisterOperand(TRITON_X86_REG_YMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM12",  PyRegisterOperand(TRITON_X86_REG_YMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM13",  PyRegisterOperand(TRITON_X86_REG_YMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM14",  PyRegisterOperand(TRITON_X86_REG_YMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM15",  PyRegisterOperand(TRITON_X86_REG_YMM15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM2",   PyRegisterOperand(TRITON_X86_REG_YMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM3",   PyRegisterOperand(TRITON_X86_REG_YMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM4",   PyRegisterOperand(TRITON_X86_REG_YMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM5",   PyRegisterOperand(TRITON_X86_REG_YMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM6",   PyRegisterOperand(TRITON_X86_REG_YMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM7",   PyRegisterOperand(TRITON_X86_REG_YMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM8",   PyRegisterOperand(TRITON_X86_REG_YMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM9",   PyRegisterOperand(TRITON_X86_REG_YMM9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZE",     PyRegisterOperand(TRITON_X86_REG_ZE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZF",     PyRegisterOperand(TRITON_X86_REG_ZF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZM",     PyRegisterOperand(TRITON_X86_REG_ZM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM0",   PyRegisterOperand(TRITON_X86_REG_ZMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM1",   PyRegisterOperand(TRITON_X86_REG_ZMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM10",  PyRegisterOperand(TRITON_X86_REG_ZMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM11",  PyRegisterOperand(TRITON_X86_REG_ZMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM12",  PyRegisterOperand(TRITON_X86_REG_ZMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM13",  PyRegisterOperand(TRITON_X86_REG_ZMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM14",  PyRegisterOperand(TRITON_X86_REG_ZMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM15",  PyRegisterOperand(TRITON_X86_REG_ZMM15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM16",  PyRegisterOperand(TRITON_X86_REG_ZMM16));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM17",  PyRegisterOperand(TRITON_X86_REG_ZMM17));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM18",  PyRegisterOperand(TRITON_X86_REG_ZMM18));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM19",  PyRegisterOperand(TRITON_X86_REG_ZMM19));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM2",   PyRegisterOperand(TRITON_X86_REG_ZMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM20",  PyRegisterOperand(TRITON_X86_REG_ZMM20));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM21",  PyRegisterOperand(TRITON_X86_REG_ZMM21));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM22",  PyRegisterOperand(TRITON_X86_REG_ZMM22));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM23",  PyRegisterOperand(TRITON_X86_REG_ZMM23));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM24",  PyRegisterOperand(TRITON_X86_REG_ZMM24));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM25",  PyRegisterOperand(TRITON_X86_REG_ZMM25));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM26",  PyRegisterOperand(TRITON_X86_REG_ZMM26));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM27",  PyRegisterOperand(TRITON_X86_REG_ZMM27));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM28",  PyRegisterOperand(TRITON_X86_REG_ZMM28));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM29",  PyRegisterOperand(TRITON_X86_REG_ZMM29));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM3",   PyRegisterOperand(TRITON_X86_REG_ZMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM30",  PyRegisterOperand(TRITON_X86_REG_ZMM30));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM31",  PyRegisterOperand(TRITON_X86_REG_ZMM31));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM4",   PyRegisterOperand(TRITON_X86_REG_ZMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM5",   PyRegisterOperand(TRITON_X86_REG_ZMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM6",   PyRegisterOperand(TRITON_X86_REG_ZMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM7",   PyRegisterOperand(TRITON_X86_REG_ZMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM8",   PyRegisterOperand(TRITON_X86_REG_ZMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM9",   PyRegisterOperand(TRITON_X86_REG_ZMM9));
            break;

          case triton::arch::ARCH_X86:
            PyDict_SetItemString(triton::bindings::python::registersDict, "AF",     PyRegisterOperand(TRITON_X86_REG_AF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AH",     PyRegisterOperand(TRITON_X86_REG_AH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AL",     PyRegisterOperand(TRITON_X86_REG_AL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AX",     PyRegisterOperand(TRITON_X86_REG_AX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BH",     PyRegisterOperand(TRITON_X86_REG_BH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BL",     PyRegisterOperand(TRITON_X86_REG_BL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BP",     PyRegisterOperand(TRITON_X86_REG_BP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BPL",    PyRegisterOperand(TRITON_X86_REG_BPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BX",     PyRegisterOperand(TRITON_X86_REG_BX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CF",     PyRegisterOperand(TRITON_X86_REG_CF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CH",     PyRegisterOperand(TRITON_X86_REG_CH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CL",     PyRegisterOperand(TRITON_X86_REG_CL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR0",    PyRegisterOperand(TRITON_X86_REG_CR0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR1",    PyRegisterOperand(TRITON_X86_REG_CR1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR10",   PyRegisterOperand(TRITON_X86_REG_CR10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR11",   PyRegisterOperand(TRITON_X86_REG_CR11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR12",   PyRegisterOperand(TRITON_X86_REG_CR12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR13",   PyRegisterOperand(TRITON_X86_REG_CR13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR14",   PyRegisterOperand(TRITON_X86_REG_CR14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR15",   PyRegisterOperand(TRITON_X86_REG_CR15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR2",    PyRegisterOperand(TRITON_X86_REG_CR2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR3",    PyRegisterOperand(TRITON_X86_REG_CR3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR4",    PyRegisterOperand(TRITON_X86_REG_CR4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR5",    PyRegisterOperand(TRITON_X86_REG_CR5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR6",    PyRegisterOperand(TRITON_X86_REG_CR6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR7",    PyRegisterOperand(TRITON_X86_REG_CR7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR8",    PyRegisterOperand(TRITON_X86_REG_CR8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR9",    PyRegisterOperand(TRITON_X86_REG_CR9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CS",     PyRegisterOperand(TRITON_X86_REG_CS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CX",     PyRegisterOperand(TRITON_X86_REG_CX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DAZ",    PyRegisterOperand(TRITON_X86_REG_DAZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DE",     PyRegisterOperand(TRITON_X86_REG_DE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DF",     PyRegisterOperand(TRITON_X86_REG_DF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DH",     PyRegisterOperand(TRITON_X86_REG_DH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DI",     PyRegisterOperand(TRITON_X86_REG_DI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DIL",    PyRegisterOperand(TRITON_X86_REG_DIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DL",     PyRegisterOperand(TRITON_X86_REG_DL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DM",     PyRegisterOperand(TRITON_X86_REG_DM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DS",     PyRegisterOperand(TRITON_X86_REG_DS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DX",     PyRegisterOperand(TRITON_X86_REG_DX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EAX",    PyRegisterOperand(TRITON_X86_REG_EAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBP",    PyRegisterOperand(TRITON_X86_REG_EBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBX",    PyRegisterOperand(TRITON_X86_REG_EBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ECX",    PyRegisterOperand(TRITON_X86_REG_ECX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDI",    PyRegisterOperand(TRITON_X86_REG_EDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDX",    PyRegisterOperand(TRITON_X86_REG_EDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EFLAGS", PyRegisterOperand(TRITON_X86_REG_EFLAGS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EIP",    PyRegisterOperand(TRITON_X86_REG_EIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ES",     PyRegisterOperand(TRITON_X86_REG_ES));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESI",    PyRegisterOperand(TRITON_X86_REG_ESI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESP",    PyRegisterOperand(TRITON_X86_REG_ESP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FS",     PyRegisterOperand(TRITON_X86_REG_FS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FZ",     PyRegisterOperand(TRITON_X86_REG_FZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "GS",     PyRegisterOperand(TRITON_X86_REG_GS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IE",     PyRegisterOperand(TRITON_X86_REG_IE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IF",     PyRegisterOperand(TRITON_X86_REG_IF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IM",     PyRegisterOperand(TRITON_X86_REG_IM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IP",     PyRegisterOperand(TRITON_X86_REG_IP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM0",    PyRegisterOperand(TRITON_X86_REG_MM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM1",    PyRegisterOperand(TRITON_X86_REG_MM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM2",    PyRegisterOperand(TRITON_X86_REG_MM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM3",    PyRegisterOperand(TRITON_X86_REG_MM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM4",    PyRegisterOperand(TRITON_X86_REG_MM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM5",    PyRegisterOperand(TRITON_X86_REG_MM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM6",    PyRegisterOperand(TRITON_X86_REG_MM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM7",    PyRegisterOperand(TRITON_X86_REG_MM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MXCSR",  PyRegisterOperand(TRITON_X86_REG_MXCSR));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OE",     PyRegisterOperand(TRITON_X86_REG_OE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OF",     PyRegisterOperand(TRITON_X86_REG_OF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OM",     PyRegisterOperand(TRITON_X86_REG_OM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PE",     PyRegisterOperand(TRITON_X86_REG_PE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PF",     PyRegisterOperand(TRITON_X86_REG_PF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PM",     PyRegisterOperand(TRITON_X86_REG_PM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RH",     PyRegisterOperand(TRITON_X86_REG_RH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RL",     PyRegisterOperand(TRITON_X86_REG_RL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SF",     PyRegisterOperand(TRITON_X86_REG_SF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SI",     PyRegisterOperand(TRITON_X86_REG_SI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SIL",    PyRegisterOperand(TRITON_X86_REG_SIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SP",     PyRegisterOperand(TRITON_X86_REG_SP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SPL",    PyRegisterOperand(TRITON_X86_REG_SPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SS",     PyRegisterOperand(TRITON_X86_REG_SS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "TF",     PyRegisterOperand(TRITON_X86_REG_TF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UE",     PyRegisterOperand(TRITON_X86_REG_UE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UM",     PyRegisterOperand(TRITON_X86_REG_UM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM0",   PyRegisterOperand(TRITON_X86_REG_XMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM1",   PyRegisterOperand(TRITON_X86_REG_XMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM2",   PyRegisterOperand(TRITON_X86_REG_XMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM3",   PyRegisterOperand(TRITON_X86_REG_XMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM4",   PyRegisterOperand(TRITON_X86_REG_XMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM5",   PyRegisterOperand(TRITON_X86_REG_XMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM6",   PyRegisterOperand(TRITON_X86_REG_XMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM7",   PyRegisterOperand(TRITON_X86_REG_XMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM0",   PyRegisterOperand(TRITON_X86_REG_YMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM1",   PyRegisterOperand(TRITON_X86_REG_YMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM2",   PyRegisterOperand(TRITON_X86_REG_YMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM3",   PyRegisterOperand(TRITON_X86_REG_YMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM4",   PyRegisterOperand(TRITON_X86_REG_YMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM5",   PyRegisterOperand(TRITON_X86_REG_YMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM6",   PyRegisterOperand(TRITON_X86_REG_YMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM7",   PyRegisterOperand(TRITON_X86_REG_YMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZE",     PyRegisterOperand(TRITON_X86_REG_ZE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZF",     PyRegisterOperand(TRITON_X86_REG_ZF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZM",     PyRegisterOperand(TRITON_X86_REG_ZM));
            break;
        } /* switch */

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
