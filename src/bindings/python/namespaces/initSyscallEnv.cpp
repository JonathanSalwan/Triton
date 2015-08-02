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


void initLinux64Env(PyObject *);


void initSyscallEnv(PyObject *idSyscallClassDict) {
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_INVALID", PyInt_FromLong(SYSCALL_STANDARD_INVALID));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_LINUX", PyInt_FromLong(SYSCALL_STANDARD_IA32_LINUX));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32E_LINUX", PyInt_FromLong(SYSCALL_STANDARD_IA32E_LINUX));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_MAC", PyInt_FromLong(SYSCALL_STANDARD_IA32_MAC));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32E_MAC", PyInt_FromLong(SYSCALL_STANDARD_IA32E_MAC));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_WINDOWS_FAST", PyInt_FromLong(SYSCALL_STANDARD_IA32_WINDOWS_FAST));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32E_WINDOWS_FAST", PyInt_FromLong(SYSCALL_STANDARD_IA32E_WINDOWS_FAST));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_IA32_WINDOWS_ALT", PyInt_FromLong(SYSCALL_STANDARD_IA32_WINDOWS_ALT));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_WOW64", PyInt_FromLong(SYSCALL_STANDARD_WOW64));
  PyDict_SetItemString(idSyscallClassDict, "STANDARD_WINDOWS_INT", PyInt_FromLong(SYSCALL_STANDARD_WINDOWS_INT));

  // LINUX64 ---------------------

  /* Create the IDREF.SYSCALL.LINUX_64 class */
  PyObject *idLinux64ClassName = xPyString_FromString("LINUX_64");
  PyObject *idLinux64ClassDict = xPyDict_New();

  /* Add registers ref into IDREF.OPCODE_CATEGORY class */
  initLinux64Env(idLinux64ClassDict);

  /* Create the OPCODE_CATEGORY class */
  PyObject *idLinux64Class = xPyClass_New(nullptr, idLinux64ClassDict, idLinux64ClassName);

  // OPCODE_CATEGORY ---------------------

  PyDict_SetItemString(idSyscallClassDict, "LINUX_64", idLinux64Class);
}

