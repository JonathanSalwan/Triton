/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <xed-category-enum.h>


void initOpcodeCategoryEnv(PyObject *idOpcodeCategoryClassDict)
{
  PyDict_SetItemString(idOpcodeCategoryClassDict, "INVALID", PyInt_FromLong(XED_CATEGORY_INVALID));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "3DNOW", PyInt_FromLong(XED_CATEGORY_3DNOW));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AES", PyInt_FromLong(XED_CATEGORY_AES));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX", PyInt_FromLong(XED_CATEGORY_AVX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX2", PyInt_FromLong(XED_CATEGORY_AVX2));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX2GATHER", PyInt_FromLong(XED_CATEGORY_AVX2GATHER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX512", PyInt_FromLong(XED_CATEGORY_AVX512));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX512VBMI", PyInt_FromLong(XED_CATEGORY_AVX512VBMI));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BDW", PyInt_FromLong(XED_CATEGORY_BDW));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BINARY", PyInt_FromLong(XED_CATEGORY_BINARY));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BITBYTE", PyInt_FromLong(XED_CATEGORY_BITBYTE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BLEND", PyInt_FromLong(XED_CATEGORY_BLEND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BMI1", PyInt_FromLong(XED_CATEGORY_BMI1));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BMI2", PyInt_FromLong(XED_CATEGORY_BMI2));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BROADCAST", PyInt_FromLong(XED_CATEGORY_BROADCAST));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CALL", PyInt_FromLong(XED_CATEGORY_CALL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CLFLUSHOPT", PyInt_FromLong(XED_CATEGORY_CLFLUSHOPT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CLWB", PyInt_FromLong(XED_CATEGORY_CLWB));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CMOV", PyInt_FromLong(XED_CATEGORY_CMOV));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "COMPRESS", PyInt_FromLong(XED_CATEGORY_COMPRESS));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "COND_BR", PyInt_FromLong(XED_CATEGORY_COND_BR));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CONFLICT", PyInt_FromLong(XED_CATEGORY_CONFLICT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CONVERT", PyInt_FromLong(XED_CATEGORY_CONVERT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "DATAXFER", PyInt_FromLong(XED_CATEGORY_DATAXFER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "DECIMAL", PyInt_FromLong(XED_CATEGORY_DECIMAL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "EXPAND", PyInt_FromLong(XED_CATEGORY_EXPAND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "FCMOV", PyInt_FromLong(XED_CATEGORY_FCMOV));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "FLAGOP", PyInt_FromLong(XED_CATEGORY_FLAGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "FMA4", PyInt_FromLong(XED_CATEGORY_FMA4));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "GATHER", PyInt_FromLong(XED_CATEGORY_GATHER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "IFMA", PyInt_FromLong(XED_CATEGORY_IFMA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "INTERRUPT", PyInt_FromLong(XED_CATEGORY_INTERRUPT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "IO", PyInt_FromLong(XED_CATEGORY_IO));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "IOSTRINGOP", PyInt_FromLong(XED_CATEGORY_IOSTRINGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "KMASK", PyInt_FromLong(XED_CATEGORY_KMASK));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "KNL", PyInt_FromLong(XED_CATEGORY_KNL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "LOGICAL", PyInt_FromLong(XED_CATEGORY_LOGICAL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "LOGICAL_FP", PyInt_FromLong(XED_CATEGORY_LOGICAL_FP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "LZCNT", PyInt_FromLong(XED_CATEGORY_LZCNT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "MISC", PyInt_FromLong(XED_CATEGORY_MISC));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "MMX", PyInt_FromLong(XED_CATEGORY_MMX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "MPX", PyInt_FromLong(XED_CATEGORY_MPX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "NOP", PyInt_FromLong(XED_CATEGORY_NOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PCLMULQDQ", PyInt_FromLong(XED_CATEGORY_PCLMULQDQ));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PCOMMIT", PyInt_FromLong(XED_CATEGORY_PCOMMIT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "POP", PyInt_FromLong(XED_CATEGORY_POP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PREFETCH", PyInt_FromLong(XED_CATEGORY_PREFETCH));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PUSH", PyInt_FromLong(XED_CATEGORY_PUSH));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RDRAND", PyInt_FromLong(XED_CATEGORY_RDRAND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RDSEED", PyInt_FromLong(XED_CATEGORY_RDSEED));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RDWRFSGS", PyInt_FromLong(XED_CATEGORY_RDWRFSGS));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RET", PyInt_FromLong(XED_CATEGORY_RET));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "ROTATE", PyInt_FromLong(XED_CATEGORY_ROTATE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SCATTER", PyInt_FromLong(XED_CATEGORY_SCATTER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SEGOP", PyInt_FromLong(XED_CATEGORY_SEGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SEMAPHORE", PyInt_FromLong(XED_CATEGORY_SEMAPHORE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SETCC", PyInt_FromLong(XED_CATEGORY_SETCC));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SGX", PyInt_FromLong(XED_CATEGORY_SGX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SHA", PyInt_FromLong(XED_CATEGORY_SHA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SHIFT", PyInt_FromLong(XED_CATEGORY_SHIFT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SMAP", PyInt_FromLong(XED_CATEGORY_SMAP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SSE", PyInt_FromLong(XED_CATEGORY_SSE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "STRINGOP", PyInt_FromLong(XED_CATEGORY_STRINGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "STTNI", PyInt_FromLong(XED_CATEGORY_STTNI));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SYSCALL", PyInt_FromLong(XED_CATEGORY_SYSCALL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SYSRET", PyInt_FromLong(XED_CATEGORY_SYSRET));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SYSTEM", PyInt_FromLong(XED_CATEGORY_SYSTEM));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "TBM", PyInt_FromLong(XED_CATEGORY_TBM));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "UNCOND_BR", PyInt_FromLong(XED_CATEGORY_UNCOND_BR));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "VFMA", PyInt_FromLong(XED_CATEGORY_VFMA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "VTX", PyInt_FromLong(XED_CATEGORY_VTX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "WIDENOP", PyInt_FromLong(XED_CATEGORY_WIDENOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "X87_ALU", PyInt_FromLong(XED_CATEGORY_X87_ALU));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XOP", PyInt_FromLong(XED_CATEGORY_XOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XSAVE", PyInt_FromLong(XED_CATEGORY_XSAVE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XSAVEOPT", PyInt_FromLong(XED_CATEGORY_XSAVEOPT));
}

