/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <csignal>
#include <python2.7/Python.h>

#include <PythonBindings.h>


void initSignalEnv(PyObject *idSignalClassDict) {
  PyDict_SetItemString(idSignalClassDict, "SIGHUP ", PyLong_FromUint(SIGHUP));
  PyDict_SetItemString(idSignalClassDict, "SIGINT ", PyLong_FromUint(SIGINT));
  PyDict_SetItemString(idSignalClassDict, "SIGQUIT", PyLong_FromUint(SIGQUIT));
  PyDict_SetItemString(idSignalClassDict, "SIGILL ", PyLong_FromUint(SIGILL));
  PyDict_SetItemString(idSignalClassDict, "SIGABRT", PyLong_FromUint(SIGABRT));
  PyDict_SetItemString(idSignalClassDict, "SIGFPE ", PyLong_FromUint(SIGFPE));
  PyDict_SetItemString(idSignalClassDict, "SIGKILL", PyLong_FromUint(SIGKILL));
  PyDict_SetItemString(idSignalClassDict, "SIGSEGV", PyLong_FromUint(SIGSEGV));
  PyDict_SetItemString(idSignalClassDict, "SIGPIPE", PyLong_FromUint(SIGPIPE));
  PyDict_SetItemString(idSignalClassDict, "SIGALRM", PyLong_FromUint(SIGALRM));
  PyDict_SetItemString(idSignalClassDict, "SIGTERM", PyLong_FromUint(SIGTERM));
}

