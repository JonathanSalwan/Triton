/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#include <python2.7/Python.h>

#include <PythonBindings.h>
#include <xed-category-enum.h>


void initOpcodeCategoryEnv(PyObject *idOpcodeCategoryClassDict) {
  PyDict_SetItemString(idOpcodeCategoryClassDict, "INVALID", PyLong_FromUint(XED_CATEGORY_INVALID));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "3DNOW", PyLong_FromUint(XED_CATEGORY_3DNOW));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AES", PyLong_FromUint(XED_CATEGORY_AES));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX", PyLong_FromUint(XED_CATEGORY_AVX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX2", PyLong_FromUint(XED_CATEGORY_AVX2));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX2GATHER", PyLong_FromUint(XED_CATEGORY_AVX2GATHER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX512", PyLong_FromUint(XED_CATEGORY_AVX512));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "AVX512VBMI", PyLong_FromUint(XED_CATEGORY_AVX512VBMI));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BDW", PyLong_FromUint(XED_CATEGORY_BDW));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BINARY", PyLong_FromUint(XED_CATEGORY_BINARY));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BITBYTE", PyLong_FromUint(XED_CATEGORY_BITBYTE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BLEND", PyLong_FromUint(XED_CATEGORY_BLEND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BMI1", PyLong_FromUint(XED_CATEGORY_BMI1));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BMI2", PyLong_FromUint(XED_CATEGORY_BMI2));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "BROADCAST", PyLong_FromUint(XED_CATEGORY_BROADCAST));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CALL", PyLong_FromUint(XED_CATEGORY_CALL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CLFLUSHOPT", PyLong_FromUint(XED_CATEGORY_CLFLUSHOPT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CLWB", PyLong_FromUint(XED_CATEGORY_CLWB));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CMOV", PyLong_FromUint(XED_CATEGORY_CMOV));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "COMPRESS", PyLong_FromUint(XED_CATEGORY_COMPRESS));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "COND_BR", PyLong_FromUint(XED_CATEGORY_COND_BR));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CONFLICT", PyLong_FromUint(XED_CATEGORY_CONFLICT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "CONVERT", PyLong_FromUint(XED_CATEGORY_CONVERT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "DATAXFER", PyLong_FromUint(XED_CATEGORY_DATAXFER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "DECIMAL", PyLong_FromUint(XED_CATEGORY_DECIMAL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "EXPAND", PyLong_FromUint(XED_CATEGORY_EXPAND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "FCMOV", PyLong_FromUint(XED_CATEGORY_FCMOV));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "FLAGOP", PyLong_FromUint(XED_CATEGORY_FLAGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "FMA4", PyLong_FromUint(XED_CATEGORY_FMA4));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "GATHER", PyLong_FromUint(XED_CATEGORY_GATHER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "IFMA", PyLong_FromUint(XED_CATEGORY_IFMA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "INTERRUPT", PyLong_FromUint(XED_CATEGORY_INTERRUPT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "IO", PyLong_FromUint(XED_CATEGORY_IO));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "IOSTRINGOP", PyLong_FromUint(XED_CATEGORY_IOSTRINGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "KMASK", PyLong_FromUint(XED_CATEGORY_KMASK));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "KNL", PyLong_FromUint(XED_CATEGORY_KNL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "LOGICAL", PyLong_FromUint(XED_CATEGORY_LOGICAL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "LOGICAL_FP", PyLong_FromUint(XED_CATEGORY_LOGICAL_FP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "LZCNT", PyLong_FromUint(XED_CATEGORY_LZCNT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "MISC", PyLong_FromUint(XED_CATEGORY_MISC));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "MMX", PyLong_FromUint(XED_CATEGORY_MMX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "MPX", PyLong_FromUint(XED_CATEGORY_MPX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "NOP", PyLong_FromUint(XED_CATEGORY_NOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PCLMULQDQ", PyLong_FromUint(XED_CATEGORY_PCLMULQDQ));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PCOMMIT", PyLong_FromUint(XED_CATEGORY_PCOMMIT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "POP", PyLong_FromUint(XED_CATEGORY_POP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PREFETCH", PyLong_FromUint(XED_CATEGORY_PREFETCH));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "PUSH", PyLong_FromUint(XED_CATEGORY_PUSH));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RDRAND", PyLong_FromUint(XED_CATEGORY_RDRAND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RDSEED", PyLong_FromUint(XED_CATEGORY_RDSEED));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RDWRFSGS", PyLong_FromUint(XED_CATEGORY_RDWRFSGS));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "RET", PyLong_FromUint(XED_CATEGORY_RET));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "ROTATE", PyLong_FromUint(XED_CATEGORY_ROTATE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SCATTER", PyLong_FromUint(XED_CATEGORY_SCATTER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SEGOP", PyLong_FromUint(XED_CATEGORY_SEGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SEMAPHORE", PyLong_FromUint(XED_CATEGORY_SEMAPHORE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SETCC", PyLong_FromUint(XED_CATEGORY_SETCC));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SGX", PyLong_FromUint(XED_CATEGORY_SGX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SHA", PyLong_FromUint(XED_CATEGORY_SHA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SHIFT", PyLong_FromUint(XED_CATEGORY_SHIFT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SMAP", PyLong_FromUint(XED_CATEGORY_SMAP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SSE", PyLong_FromUint(XED_CATEGORY_SSE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "STRINGOP", PyLong_FromUint(XED_CATEGORY_STRINGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "STTNI", PyLong_FromUint(XED_CATEGORY_STTNI));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SYSCALL", PyLong_FromUint(XED_CATEGORY_SYSCALL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SYSRET", PyLong_FromUint(XED_CATEGORY_SYSRET));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "SYSTEM", PyLong_FromUint(XED_CATEGORY_SYSTEM));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "TBM", PyLong_FromUint(XED_CATEGORY_TBM));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "UNCOND_BR", PyLong_FromUint(XED_CATEGORY_UNCOND_BR));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "VFMA", PyLong_FromUint(XED_CATEGORY_VFMA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "VTX", PyLong_FromUint(XED_CATEGORY_VTX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "WIDENOP", PyLong_FromUint(XED_CATEGORY_WIDENOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "X87_ALU", PyLong_FromUint(XED_CATEGORY_X87_ALU));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XOP", PyLong_FromUint(XED_CATEGORY_XOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XSAVE", PyLong_FromUint(XED_CATEGORY_XSAVE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XSAVEOPT", PyLong_FromUint(XED_CATEGORY_XSAVEOPT));
}

