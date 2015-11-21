/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <Registers.h>


void initRegEnv(PyObject *idRegClassDict) {
  PyDict_SetItemString(idRegClassDict, "INVALID", PyLong_FromUint(ID_INVALID));
  #if defined(__x86_64__) || defined(_M_X64)
  PyDict_SetItemString(idRegClassDict, "RAX", PyLong_FromUint(ID_RAX));
  PyDict_SetItemString(idRegClassDict, "RBX", PyLong_FromUint(ID_RBX));
  PyDict_SetItemString(idRegClassDict, "RCX", PyLong_FromUint(ID_RCX));
  PyDict_SetItemString(idRegClassDict, "RDX", PyLong_FromUint(ID_RDX));
  PyDict_SetItemString(idRegClassDict, "RDI", PyLong_FromUint(ID_RDI));
  PyDict_SetItemString(idRegClassDict, "RSI", PyLong_FromUint(ID_RSI));
  PyDict_SetItemString(idRegClassDict, "RBP", PyLong_FromUint(ID_RBP));
  PyDict_SetItemString(idRegClassDict, "RSP", PyLong_FromUint(ID_RSP));
  PyDict_SetItemString(idRegClassDict, "RIP", PyLong_FromUint(ID_RIP));
  PyDict_SetItemString(idRegClassDict, "RFLAGS", PyLong_FromUint(ID_RFLAGS));
  #endif

  #if defined(__i386) || defined(_M_IX86)
  PyDict_SetItemString(idRegClassDict, "EAX", PyLong_FromUint(ID_EAX));
  PyDict_SetItemString(idRegClassDict, "EBX", PyLong_FromUint(ID_EBX));
  PyDict_SetItemString(idRegClassDict, "ECX", PyLong_FromUint(ID_ECX));
  PyDict_SetItemString(idRegClassDict, "EDX", PyLong_FromUint(ID_EDX));
  PyDict_SetItemString(idRegClassDict, "EDI", PyLong_FromUint(ID_EDI));
  PyDict_SetItemString(idRegClassDict, "ESI", PyLong_FromUint(ID_ESI));
  PyDict_SetItemString(idRegClassDict, "EBP", PyLong_FromUint(ID_EBP));
  PyDict_SetItemString(idRegClassDict, "ESP", PyLong_FromUint(ID_ESP));
  PyDict_SetItemString(idRegClassDict, "EIP", PyLong_FromUint(ID_EIP));
  PyDict_SetItemString(idRegClassDict, "EFLAGS", PyLong_FromUint(ID_EFLAGS));
  #endif

  #if defined(__x86_64__) || defined(_M_X64)
  PyDict_SetItemString(idRegClassDict, "R8", PyLong_FromUint(ID_R8));
  PyDict_SetItemString(idRegClassDict, "R9", PyLong_FromUint(ID_R9));
  PyDict_SetItemString(idRegClassDict, "R10", PyLong_FromUint(ID_R10));
  PyDict_SetItemString(idRegClassDict, "R11", PyLong_FromUint(ID_R11));
  PyDict_SetItemString(idRegClassDict, "R12", PyLong_FromUint(ID_R12));
  PyDict_SetItemString(idRegClassDict, "R13", PyLong_FromUint(ID_R13));
  PyDict_SetItemString(idRegClassDict, "R14", PyLong_FromUint(ID_R14));
  PyDict_SetItemString(idRegClassDict, "R15", PyLong_FromUint(ID_R15));
  #endif

  PyDict_SetItemString(idRegClassDict, "XMM0", PyLong_FromUint(ID_XMM0));
  PyDict_SetItemString(idRegClassDict, "XMM1", PyLong_FromUint(ID_XMM1));
  PyDict_SetItemString(idRegClassDict, "XMM2", PyLong_FromUint(ID_XMM2));
  PyDict_SetItemString(idRegClassDict, "XMM3", PyLong_FromUint(ID_XMM3));
  PyDict_SetItemString(idRegClassDict, "XMM4", PyLong_FromUint(ID_XMM4));
  PyDict_SetItemString(idRegClassDict, "XMM5", PyLong_FromUint(ID_XMM5));
  PyDict_SetItemString(idRegClassDict, "XMM6", PyLong_FromUint(ID_XMM6));
  PyDict_SetItemString(idRegClassDict, "XMM7", PyLong_FromUint(ID_XMM7));

  #if defined(__x86_64__) || defined(_M_X64)
  PyDict_SetItemString(idRegClassDict, "XMM8", PyLong_FromUint(ID_XMM8));
  PyDict_SetItemString(idRegClassDict, "XMM9", PyLong_FromUint(ID_XMM9));
  PyDict_SetItemString(idRegClassDict, "XMM10", PyLong_FromUint(ID_XMM10));
  PyDict_SetItemString(idRegClassDict, "XMM11", PyLong_FromUint(ID_XMM11));
  PyDict_SetItemString(idRegClassDict, "XMM12", PyLong_FromUint(ID_XMM12));
  PyDict_SetItemString(idRegClassDict, "XMM13", PyLong_FromUint(ID_XMM13));
  PyDict_SetItemString(idRegClassDict, "XMM14", PyLong_FromUint(ID_XMM14));
  PyDict_SetItemString(idRegClassDict, "XMM15", PyLong_FromUint(ID_XMM15));
  #endif
}
