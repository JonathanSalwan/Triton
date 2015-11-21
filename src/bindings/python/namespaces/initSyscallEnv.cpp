/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <IRBuilderOperand.h>
#include <PythonBindings.h>
#include <xPyFunc.h>

#include <pin.H>


void initLinuxEnv(PyObject *);


void initSyscallEnv(PyObject *idSyscallClassDict) {
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_INVALID", PyLong_FromUint(SYSCALL_STANDARD_INVALID));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_LINUX", PyLong_FromUint(SYSCALL_STANDARD_IA32_LINUX));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32E_LINUX", PyLong_FromUint(SYSCALL_STANDARD_IA32E_LINUX));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_MAC", PyLong_FromUint(SYSCALL_STANDARD_IA32_MAC));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32E_MAC", PyLong_FromUint(SYSCALL_STANDARD_IA32E_MAC));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_WINDOWS_FAST", PyLong_FromUint(SYSCALL_STANDARD_IA32_WINDOWS_FAST));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32E_WINDOWS_FAST", PyLong_FromUint(SYSCALL_STANDARD_IA32E_WINDOWS_FAST));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_WINDOWS_ALT", PyLong_FromUint(SYSCALL_STANDARD_IA32_WINDOWS_ALT));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_WOW64", PyLong_FromUint(SYSCALL_STANDARD_WOW64));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_WINDOWS_INT", PyLong_FromUint(SYSCALL_STANDARD_WINDOWS_INT));

  // LINUX{32|64} ---------------------

  /* Create the IDREF.SYSCALL.LINUX_{32|64} class */
  #if defined(__x86_64__) || defined(_M_X64)
  PyObject *idLinuxClassName = xPyString_FromString("LINUX_64");
  #endif
  #if defined(__i386) || defined(_M_IX86)
  PyObject *idLinuxClassName = xPyString_FromString("LINUX_32");
  #endif
  PyObject *idLinuxClassDict = xPyDict_New();

  /* Add registers ref into IDREF.OPCODE_CATEGORY class */
  initLinuxEnv(idLinuxClassDict);

  /* Create the OPCODE_CATEGORY class */
  PyObject *idLinuxClass = xPyClass_New(nullptr, idLinuxClassDict, idLinuxClassName);

  // OPCODE_CATEGORY ---------------------

  #if defined(__x86_64__) || defined(_M_X64)
  PyDict_SetItemString(idSyscallClassDict, "LINUX_64", idLinuxClass);
  #endif
  #if defined(__i386) || defined(_M_IX86)
  PyDict_SetItemString(idSyscallClassDict, "LINUX_32", idLinuxClass);
  #endif
}

