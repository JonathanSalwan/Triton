/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef   PYTHONUTILS_H
#define   PYTHONUTILS_H

#include "TritonTypes.h"
#include <python2.7/Python.h>

uint128   PyLongObjectToUint128(PyObject *obj);
PyObject  *uint128ToPyLongObject(uint128 value);
PyObject  *uint512ToPyLongObject(uint512 value);

#if defined(__x86_64__) || defined(_M_X64)
  #define PyLong_AsUint     PyLong_AsLongLong
  #define PyLong_FromUint   PyLong_FromLongLong
#endif

#if defined(__i386) || defined(_M_IX86)
  #define PyLong_AsUint     PyLong_AsLong
  #define PyLong_FromUint   PyLong_FromLong
#endif

#endif     /* !PYTHONUTILS_H */
