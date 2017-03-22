//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/api.hpp>
#include <triton/architecture.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonObjects.hpp>
#include <triton/x86Specifications.hpp>



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
#define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)\
            PyDict_SetItemString(triton::bindings::python::registersDict, #UPPER_NAME, PyRegister(triton::arch::Register(triton::api.getRegister(triton::arch::ID_REG_##UPPER_NAME), 0x00)));
#define REG_SPEC_NO_CAPSTONE REG_SPEC
#include "triton/x86.spec"
            break;

          case triton::arch::ARCH_X86:
#define REG_SPEC(UPPER_NAME, LOWER_NAME, X86_64_UPPER, X86_64_LOWER, X86_64_PARENT, X86_UPPER, X86_LOWER, X86_PARENT, X86_AVAIL)\
          if(X86_AVAIL)\
            PyDict_SetItemString(triton::bindings::python::registersDict, #UPPER_NAME, PyRegister(triton::arch::Register(triton::api.getRegister(triton::arch::ID_REG_##UPPER_NAME), 0x00)));
#define REG_SPEC_NO_CAPSTONE REG_SPEC
#include "triton/x86.spec"
            break;
        } /* switch */

      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
