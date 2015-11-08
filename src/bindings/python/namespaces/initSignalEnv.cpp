/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <csignal>
#include <python2.7/Python.h>

#include <PythonBindings.h>


void initSignalEnv(PyObject *idSignalClassDict) {
  PyDict_SetItemString(idSignalClassDict, "SIGHUP ", PyLong_FromLongLong(SIGHUP));
  PyDict_SetItemString(idSignalClassDict, "SIGINT ", PyLong_FromLongLong(SIGINT));
  PyDict_SetItemString(idSignalClassDict, "SIGQUIT", PyLong_FromLongLong(SIGQUIT));
  PyDict_SetItemString(idSignalClassDict, "SIGILL ", PyLong_FromLongLong(SIGILL));
  PyDict_SetItemString(idSignalClassDict, "SIGABRT", PyLong_FromLongLong(SIGABRT));
  PyDict_SetItemString(idSignalClassDict, "SIGFPE ", PyLong_FromLongLong(SIGFPE));
  PyDict_SetItemString(idSignalClassDict, "SIGKILL", PyLong_FromLongLong(SIGKILL));
  PyDict_SetItemString(idSignalClassDict, "SIGSEGV", PyLong_FromLongLong(SIGSEGV));
  PyDict_SetItemString(idSignalClassDict, "SIGPIPE", PyLong_FromLongLong(SIGPIPE));
  PyDict_SetItemString(idSignalClassDict, "SIGALRM", PyLong_FromLongLong(SIGALRM));
  PyDict_SetItemString(idSignalClassDict, "SIGTERM", PyLong_FromLongLong(SIGTERM));
}

