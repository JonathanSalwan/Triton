
#include <python2.7/Python.h>

#include "IRBuilderOperand.h"
#include "PythonBindings.h"

#include "pin.H"


void initSyscallEnv(PyObject *idSyscallClassDict)
{
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
}

