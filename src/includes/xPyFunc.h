
#ifndef   XPYFUNC_H
#define   XPYFUNC_H

#include <python2.7/Python.h>

PyObject *xPyClass_New(PyObject *b, PyObject *d, PyObject *n);
PyObject *xPyDict_New(void);
PyObject *xPyList_New(Py_ssize_t len);
PyObject *xPyString_FromString(const char *v);
PyObject *xPyTuple_New(Py_ssize_t len);

#endif     /* !__XPYFUNC_H__ */
