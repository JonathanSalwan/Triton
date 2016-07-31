//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
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
            PyDict_SetItemString(triton::bindings::python::registersDict, "AF",     PyRegister(TRITON_X86_REG_AF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AH",     PyRegister(TRITON_X86_REG_AH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AL",     PyRegister(TRITON_X86_REG_AL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AX",     PyRegister(TRITON_X86_REG_AX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BH",     PyRegister(TRITON_X86_REG_BH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BL",     PyRegister(TRITON_X86_REG_BL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BP",     PyRegister(TRITON_X86_REG_BP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BPL",    PyRegister(TRITON_X86_REG_BPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BX",     PyRegister(TRITON_X86_REG_BX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CF",     PyRegister(TRITON_X86_REG_CF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CH",     PyRegister(TRITON_X86_REG_CH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CL",     PyRegister(TRITON_X86_REG_CL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR0",    PyRegister(TRITON_X86_REG_CR0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR1",    PyRegister(TRITON_X86_REG_CR1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR10",   PyRegister(TRITON_X86_REG_CR10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR11",   PyRegister(TRITON_X86_REG_CR11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR12",   PyRegister(TRITON_X86_REG_CR12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR13",   PyRegister(TRITON_X86_REG_CR13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR14",   PyRegister(TRITON_X86_REG_CR14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR15",   PyRegister(TRITON_X86_REG_CR15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR2",    PyRegister(TRITON_X86_REG_CR2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR3",    PyRegister(TRITON_X86_REG_CR3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR4",    PyRegister(TRITON_X86_REG_CR4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR5",    PyRegister(TRITON_X86_REG_CR5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR6",    PyRegister(TRITON_X86_REG_CR6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR7",    PyRegister(TRITON_X86_REG_CR7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR8",    PyRegister(TRITON_X86_REG_CR8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR9",    PyRegister(TRITON_X86_REG_CR9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CS",     PyRegister(TRITON_X86_REG_CS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CX",     PyRegister(TRITON_X86_REG_CX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DAZ",    PyRegister(TRITON_X86_REG_DAZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DE",     PyRegister(TRITON_X86_REG_DE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DF",     PyRegister(TRITON_X86_REG_DF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DH",     PyRegister(TRITON_X86_REG_DH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DI",     PyRegister(TRITON_X86_REG_DI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DIL",    PyRegister(TRITON_X86_REG_DIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DL",     PyRegister(TRITON_X86_REG_DL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DM",     PyRegister(TRITON_X86_REG_DM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DS",     PyRegister(TRITON_X86_REG_DS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DX",     PyRegister(TRITON_X86_REG_DX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EAX",    PyRegister(TRITON_X86_REG_EAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBP",    PyRegister(TRITON_X86_REG_EBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBX",    PyRegister(TRITON_X86_REG_EBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ECX",    PyRegister(TRITON_X86_REG_ECX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDI",    PyRegister(TRITON_X86_REG_EDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDX",    PyRegister(TRITON_X86_REG_EDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EFLAGS", PyRegister(TRITON_X86_REG_EFLAGS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EIP",    PyRegister(TRITON_X86_REG_EIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ES",     PyRegister(TRITON_X86_REG_ES));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESI",    PyRegister(TRITON_X86_REG_ESI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESP",    PyRegister(TRITON_X86_REG_ESP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FS",     PyRegister(TRITON_X86_REG_FS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FZ",     PyRegister(TRITON_X86_REG_FZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "GS",     PyRegister(TRITON_X86_REG_GS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IE",     PyRegister(TRITON_X86_REG_IE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IF",     PyRegister(TRITON_X86_REG_IF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IM",     PyRegister(TRITON_X86_REG_IM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IP",     PyRegister(TRITON_X86_REG_IP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM0",    PyRegister(TRITON_X86_REG_MM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM1",    PyRegister(TRITON_X86_REG_MM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM2",    PyRegister(TRITON_X86_REG_MM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM3",    PyRegister(TRITON_X86_REG_MM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM4",    PyRegister(TRITON_X86_REG_MM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM5",    PyRegister(TRITON_X86_REG_MM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM6",    PyRegister(TRITON_X86_REG_MM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM7",    PyRegister(TRITON_X86_REG_MM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MXCSR",  PyRegister(TRITON_X86_REG_MXCSR));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OE",     PyRegister(TRITON_X86_REG_OE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OF",     PyRegister(TRITON_X86_REG_OF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OM",     PyRegister(TRITON_X86_REG_OM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PE",     PyRegister(TRITON_X86_REG_PE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PF",     PyRegister(TRITON_X86_REG_PF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PM",     PyRegister(TRITON_X86_REG_PM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10",    PyRegister(TRITON_X86_REG_R10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10B",   PyRegister(TRITON_X86_REG_R10B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10D",   PyRegister(TRITON_X86_REG_R10D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R10W",   PyRegister(TRITON_X86_REG_R10W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11",    PyRegister(TRITON_X86_REG_R11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11B",   PyRegister(TRITON_X86_REG_R11B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11D",   PyRegister(TRITON_X86_REG_R11D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R11W",   PyRegister(TRITON_X86_REG_R11W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12",    PyRegister(TRITON_X86_REG_R12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12B",   PyRegister(TRITON_X86_REG_R12B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12D",   PyRegister(TRITON_X86_REG_R12D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R12W",   PyRegister(TRITON_X86_REG_R12W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13",    PyRegister(TRITON_X86_REG_R13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13B",   PyRegister(TRITON_X86_REG_R13B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13D",   PyRegister(TRITON_X86_REG_R13D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R13W",   PyRegister(TRITON_X86_REG_R13W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14",    PyRegister(TRITON_X86_REG_R14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14B",   PyRegister(TRITON_X86_REG_R14B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14D",   PyRegister(TRITON_X86_REG_R14D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R14W",   PyRegister(TRITON_X86_REG_R14W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15",    PyRegister(TRITON_X86_REG_R15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15B",   PyRegister(TRITON_X86_REG_R15B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15D",   PyRegister(TRITON_X86_REG_R15D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R15W",   PyRegister(TRITON_X86_REG_R15W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8",     PyRegister(TRITON_X86_REG_R8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8B",    PyRegister(TRITON_X86_REG_R8B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8D",    PyRegister(TRITON_X86_REG_R8D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R8W",    PyRegister(TRITON_X86_REG_R8W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9",     PyRegister(TRITON_X86_REG_R9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9B",    PyRegister(TRITON_X86_REG_R9B));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9D",    PyRegister(TRITON_X86_REG_R9D));
            PyDict_SetItemString(triton::bindings::python::registersDict, "R9W",    PyRegister(TRITON_X86_REG_R9W));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RAX",    PyRegister(TRITON_X86_REG_RAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RBP",    PyRegister(TRITON_X86_REG_RBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RBX",    PyRegister(TRITON_X86_REG_RBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RCX",    PyRegister(TRITON_X86_REG_RCX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RDI",    PyRegister(TRITON_X86_REG_RDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RDX",    PyRegister(TRITON_X86_REG_RDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RH",     PyRegister(TRITON_X86_REG_RH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RIP",    PyRegister(TRITON_X86_REG_RIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RL",     PyRegister(TRITON_X86_REG_RL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RSI",    PyRegister(TRITON_X86_REG_RSI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RSP",    PyRegister(TRITON_X86_REG_RSP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SF",     PyRegister(TRITON_X86_REG_SF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SI",     PyRegister(TRITON_X86_REG_SI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SIL",    PyRegister(TRITON_X86_REG_SIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SP",     PyRegister(TRITON_X86_REG_SP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SPL",    PyRegister(TRITON_X86_REG_SPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SS",     PyRegister(TRITON_X86_REG_SS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "TF",     PyRegister(TRITON_X86_REG_TF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UE",     PyRegister(TRITON_X86_REG_UE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UM",     PyRegister(TRITON_X86_REG_UM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM0",   PyRegister(TRITON_X86_REG_XMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM1",   PyRegister(TRITON_X86_REG_XMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM10",  PyRegister(TRITON_X86_REG_XMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM11",  PyRegister(TRITON_X86_REG_XMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM12",  PyRegister(TRITON_X86_REG_XMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM13",  PyRegister(TRITON_X86_REG_XMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM14",  PyRegister(TRITON_X86_REG_XMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM15",  PyRegister(TRITON_X86_REG_XMM15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM2",   PyRegister(TRITON_X86_REG_XMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM3",   PyRegister(TRITON_X86_REG_XMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM4",   PyRegister(TRITON_X86_REG_XMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM5",   PyRegister(TRITON_X86_REG_XMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM6",   PyRegister(TRITON_X86_REG_XMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM7",   PyRegister(TRITON_X86_REG_XMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM8",   PyRegister(TRITON_X86_REG_XMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM9",   PyRegister(TRITON_X86_REG_XMM9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM0",   PyRegister(TRITON_X86_REG_YMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM1",   PyRegister(TRITON_X86_REG_YMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM10",  PyRegister(TRITON_X86_REG_YMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM11",  PyRegister(TRITON_X86_REG_YMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM12",  PyRegister(TRITON_X86_REG_YMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM13",  PyRegister(TRITON_X86_REG_YMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM14",  PyRegister(TRITON_X86_REG_YMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM15",  PyRegister(TRITON_X86_REG_YMM15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM2",   PyRegister(TRITON_X86_REG_YMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM3",   PyRegister(TRITON_X86_REG_YMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM4",   PyRegister(TRITON_X86_REG_YMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM5",   PyRegister(TRITON_X86_REG_YMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM6",   PyRegister(TRITON_X86_REG_YMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM7",   PyRegister(TRITON_X86_REG_YMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM8",   PyRegister(TRITON_X86_REG_YMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM9",   PyRegister(TRITON_X86_REG_YMM9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZE",     PyRegister(TRITON_X86_REG_ZE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZF",     PyRegister(TRITON_X86_REG_ZF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZM",     PyRegister(TRITON_X86_REG_ZM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM0",   PyRegister(TRITON_X86_REG_ZMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM1",   PyRegister(TRITON_X86_REG_ZMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM10",  PyRegister(TRITON_X86_REG_ZMM10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM11",  PyRegister(TRITON_X86_REG_ZMM11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM12",  PyRegister(TRITON_X86_REG_ZMM12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM13",  PyRegister(TRITON_X86_REG_ZMM13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM14",  PyRegister(TRITON_X86_REG_ZMM14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM15",  PyRegister(TRITON_X86_REG_ZMM15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM16",  PyRegister(TRITON_X86_REG_ZMM16));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM17",  PyRegister(TRITON_X86_REG_ZMM17));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM18",  PyRegister(TRITON_X86_REG_ZMM18));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM19",  PyRegister(TRITON_X86_REG_ZMM19));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM2",   PyRegister(TRITON_X86_REG_ZMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM20",  PyRegister(TRITON_X86_REG_ZMM20));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM21",  PyRegister(TRITON_X86_REG_ZMM21));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM22",  PyRegister(TRITON_X86_REG_ZMM22));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM23",  PyRegister(TRITON_X86_REG_ZMM23));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM24",  PyRegister(TRITON_X86_REG_ZMM24));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM25",  PyRegister(TRITON_X86_REG_ZMM25));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM26",  PyRegister(TRITON_X86_REG_ZMM26));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM27",  PyRegister(TRITON_X86_REG_ZMM27));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM28",  PyRegister(TRITON_X86_REG_ZMM28));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM29",  PyRegister(TRITON_X86_REG_ZMM29));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM3",   PyRegister(TRITON_X86_REG_ZMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM30",  PyRegister(TRITON_X86_REG_ZMM30));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM31",  PyRegister(TRITON_X86_REG_ZMM31));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM4",   PyRegister(TRITON_X86_REG_ZMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM5",   PyRegister(TRITON_X86_REG_ZMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM6",   PyRegister(TRITON_X86_REG_ZMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM7",   PyRegister(TRITON_X86_REG_ZMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM8",   PyRegister(TRITON_X86_REG_ZMM8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZMM9",   PyRegister(TRITON_X86_REG_ZMM9));
            break;

          case triton::arch::ARCH_X86:
            PyDict_SetItemString(triton::bindings::python::registersDict, "AF",     PyRegister(TRITON_X86_REG_AF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AH",     PyRegister(TRITON_X86_REG_AH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AL",     PyRegister(TRITON_X86_REG_AL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "AX",     PyRegister(TRITON_X86_REG_AX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BH",     PyRegister(TRITON_X86_REG_BH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BL",     PyRegister(TRITON_X86_REG_BL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BP",     PyRegister(TRITON_X86_REG_BP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BPL",    PyRegister(TRITON_X86_REG_BPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "BX",     PyRegister(TRITON_X86_REG_BX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CF",     PyRegister(TRITON_X86_REG_CF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CH",     PyRegister(TRITON_X86_REG_CH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CL",     PyRegister(TRITON_X86_REG_CL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR0",    PyRegister(TRITON_X86_REG_CR0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR1",    PyRegister(TRITON_X86_REG_CR1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR10",   PyRegister(TRITON_X86_REG_CR10));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR11",   PyRegister(TRITON_X86_REG_CR11));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR12",   PyRegister(TRITON_X86_REG_CR12));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR13",   PyRegister(TRITON_X86_REG_CR13));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR14",   PyRegister(TRITON_X86_REG_CR14));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR15",   PyRegister(TRITON_X86_REG_CR15));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR2",    PyRegister(TRITON_X86_REG_CR2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR3",    PyRegister(TRITON_X86_REG_CR3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR4",    PyRegister(TRITON_X86_REG_CR4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR5",    PyRegister(TRITON_X86_REG_CR5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR6",    PyRegister(TRITON_X86_REG_CR6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR7",    PyRegister(TRITON_X86_REG_CR7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR8",    PyRegister(TRITON_X86_REG_CR8));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CR9",    PyRegister(TRITON_X86_REG_CR9));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CS",     PyRegister(TRITON_X86_REG_CS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "CX",     PyRegister(TRITON_X86_REG_CX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DAZ",    PyRegister(TRITON_X86_REG_DAZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DE",     PyRegister(TRITON_X86_REG_DE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DF",     PyRegister(TRITON_X86_REG_DF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DH",     PyRegister(TRITON_X86_REG_DH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DI",     PyRegister(TRITON_X86_REG_DI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DIL",    PyRegister(TRITON_X86_REG_DIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DL",     PyRegister(TRITON_X86_REG_DL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DM",     PyRegister(TRITON_X86_REG_DM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DS",     PyRegister(TRITON_X86_REG_DS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "DX",     PyRegister(TRITON_X86_REG_DX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EAX",    PyRegister(TRITON_X86_REG_EAX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBP",    PyRegister(TRITON_X86_REG_EBP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EBX",    PyRegister(TRITON_X86_REG_EBX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ECX",    PyRegister(TRITON_X86_REG_ECX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDI",    PyRegister(TRITON_X86_REG_EDI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EDX",    PyRegister(TRITON_X86_REG_EDX));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EFLAGS", PyRegister(TRITON_X86_REG_EFLAGS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "EIP",    PyRegister(TRITON_X86_REG_EIP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ES",     PyRegister(TRITON_X86_REG_ES));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESI",    PyRegister(TRITON_X86_REG_ESI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ESP",    PyRegister(TRITON_X86_REG_ESP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FS",     PyRegister(TRITON_X86_REG_FS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "FZ",     PyRegister(TRITON_X86_REG_FZ));
            PyDict_SetItemString(triton::bindings::python::registersDict, "GS",     PyRegister(TRITON_X86_REG_GS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IE",     PyRegister(TRITON_X86_REG_IE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IF",     PyRegister(TRITON_X86_REG_IF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IM",     PyRegister(TRITON_X86_REG_IM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "IP",     PyRegister(TRITON_X86_REG_IP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM0",    PyRegister(TRITON_X86_REG_MM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM1",    PyRegister(TRITON_X86_REG_MM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM2",    PyRegister(TRITON_X86_REG_MM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM3",    PyRegister(TRITON_X86_REG_MM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM4",    PyRegister(TRITON_X86_REG_MM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM5",    PyRegister(TRITON_X86_REG_MM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM6",    PyRegister(TRITON_X86_REG_MM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MM7",    PyRegister(TRITON_X86_REG_MM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "MXCSR",  PyRegister(TRITON_X86_REG_MXCSR));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OE",     PyRegister(TRITON_X86_REG_OE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OF",     PyRegister(TRITON_X86_REG_OF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "OM",     PyRegister(TRITON_X86_REG_OM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PE",     PyRegister(TRITON_X86_REG_PE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PF",     PyRegister(TRITON_X86_REG_PF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "PM",     PyRegister(TRITON_X86_REG_PM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RH",     PyRegister(TRITON_X86_REG_RH));
            PyDict_SetItemString(triton::bindings::python::registersDict, "RL",     PyRegister(TRITON_X86_REG_RL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SF",     PyRegister(TRITON_X86_REG_SF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SI",     PyRegister(TRITON_X86_REG_SI));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SIL",    PyRegister(TRITON_X86_REG_SIL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SP",     PyRegister(TRITON_X86_REG_SP));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SPL",    PyRegister(TRITON_X86_REG_SPL));
            PyDict_SetItemString(triton::bindings::python::registersDict, "SS",     PyRegister(TRITON_X86_REG_SS));
            PyDict_SetItemString(triton::bindings::python::registersDict, "TF",     PyRegister(TRITON_X86_REG_TF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UE",     PyRegister(TRITON_X86_REG_UE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "UM",     PyRegister(TRITON_X86_REG_UM));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM0",   PyRegister(TRITON_X86_REG_XMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM1",   PyRegister(TRITON_X86_REG_XMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM2",   PyRegister(TRITON_X86_REG_XMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM3",   PyRegister(TRITON_X86_REG_XMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM4",   PyRegister(TRITON_X86_REG_XMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM5",   PyRegister(TRITON_X86_REG_XMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM6",   PyRegister(TRITON_X86_REG_XMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "XMM7",   PyRegister(TRITON_X86_REG_XMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM0",   PyRegister(TRITON_X86_REG_YMM0));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM1",   PyRegister(TRITON_X86_REG_YMM1));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM2",   PyRegister(TRITON_X86_REG_YMM2));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM3",   PyRegister(TRITON_X86_REG_YMM3));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM4",   PyRegister(TRITON_X86_REG_YMM4));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM5",   PyRegister(TRITON_X86_REG_YMM5));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM6",   PyRegister(TRITON_X86_REG_YMM6));
            PyDict_SetItemString(triton::bindings::python::registersDict, "YMM7",   PyRegister(TRITON_X86_REG_YMM7));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZE",     PyRegister(TRITON_X86_REG_ZE));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZF",     PyRegister(TRITON_X86_REG_ZF));
            PyDict_SetItemString(triton::bindings::python::registersDict, "ZM",     PyRegister(TRITON_X86_REG_ZM));
            break;
        } /* switch */

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */

#endif /* TRITON_PYTHON_BINDINGS */
