
#include <python2.7/Python.h>

#include "PythonBindings.h"
#include "xed-category-enum.h"


void initOpcodeCategoryEnv(PyObject *idOpcodeCategoryClassDict)
{
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_INVALID", PyInt_FromLong(XED_CATEGORY_INVALID));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_3DNOW", PyInt_FromLong(XED_CATEGORY_3DNOW));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_AES", PyInt_FromLong(XED_CATEGORY_AES));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_AVX", PyInt_FromLong(XED_CATEGORY_AVX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_AVX2", PyInt_FromLong(XED_CATEGORY_AVX2));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_AVX2GATHER", PyInt_FromLong(XED_CATEGORY_AVX2GATHER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_AVX512", PyInt_FromLong(XED_CATEGORY_AVX512));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_AVX512VBMI", PyInt_FromLong(XED_CATEGORY_AVX512VBMI));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BDW", PyInt_FromLong(XED_CATEGORY_BDW));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BINARY", PyInt_FromLong(XED_CATEGORY_BINARY));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BITBYTE", PyInt_FromLong(XED_CATEGORY_BITBYTE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BLEND", PyInt_FromLong(XED_CATEGORY_BLEND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BMI1", PyInt_FromLong(XED_CATEGORY_BMI1));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BMI2", PyInt_FromLong(XED_CATEGORY_BMI2));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_BROADCAST", PyInt_FromLong(XED_CATEGORY_BROADCAST));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_CALL", PyInt_FromLong(XED_CATEGORY_CALL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_CLFLUSHOPT", PyInt_FromLong(XED_CATEGORY_CLFLUSHOPT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_CLWB", PyInt_FromLong(XED_CATEGORY_CLWB));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_CMOV", PyInt_FromLong(XED_CATEGORY_CMOV));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_COMPRESS", PyInt_FromLong(XED_CATEGORY_COMPRESS));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_COND_BR", PyInt_FromLong(XED_CATEGORY_COND_BR));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_CONFLICT", PyInt_FromLong(XED_CATEGORY_CONFLICT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_CONVERT", PyInt_FromLong(XED_CATEGORY_CONVERT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_DATAXFER", PyInt_FromLong(XED_CATEGORY_DATAXFER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_DECIMAL", PyInt_FromLong(XED_CATEGORY_DECIMAL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_EXPAND", PyInt_FromLong(XED_CATEGORY_EXPAND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_FCMOV", PyInt_FromLong(XED_CATEGORY_FCMOV));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_FLAGOP", PyInt_FromLong(XED_CATEGORY_FLAGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_FMA4", PyInt_FromLong(XED_CATEGORY_FMA4));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_GATHER", PyInt_FromLong(XED_CATEGORY_GATHER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_IFMA", PyInt_FromLong(XED_CATEGORY_IFMA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_INTERRUPT", PyInt_FromLong(XED_CATEGORY_INTERRUPT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_IO", PyInt_FromLong(XED_CATEGORY_IO));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_IOSTRINGOP", PyInt_FromLong(XED_CATEGORY_IOSTRINGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_KMASK", PyInt_FromLong(XED_CATEGORY_KMASK));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_KNL", PyInt_FromLong(XED_CATEGORY_KNL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_LOGICAL", PyInt_FromLong(XED_CATEGORY_LOGICAL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_LOGICAL_FP", PyInt_FromLong(XED_CATEGORY_LOGICAL_FP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_LZCNT", PyInt_FromLong(XED_CATEGORY_LZCNT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_MISC", PyInt_FromLong(XED_CATEGORY_MISC));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_MMX", PyInt_FromLong(XED_CATEGORY_MMX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_MPX", PyInt_FromLong(XED_CATEGORY_MPX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_NOP", PyInt_FromLong(XED_CATEGORY_NOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_PCLMULQDQ", PyInt_FromLong(XED_CATEGORY_PCLMULQDQ));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_PCOMMIT", PyInt_FromLong(XED_CATEGORY_PCOMMIT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_POP", PyInt_FromLong(XED_CATEGORY_POP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_PREFETCH", PyInt_FromLong(XED_CATEGORY_PREFETCH));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_PUSH", PyInt_FromLong(XED_CATEGORY_PUSH));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_RDRAND", PyInt_FromLong(XED_CATEGORY_RDRAND));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_RDSEED", PyInt_FromLong(XED_CATEGORY_RDSEED));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_RDWRFSGS", PyInt_FromLong(XED_CATEGORY_RDWRFSGS));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_RET", PyInt_FromLong(XED_CATEGORY_RET));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_ROTATE", PyInt_FromLong(XED_CATEGORY_ROTATE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SCATTER", PyInt_FromLong(XED_CATEGORY_SCATTER));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SEGOP", PyInt_FromLong(XED_CATEGORY_SEGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SEMAPHORE", PyInt_FromLong(XED_CATEGORY_SEMAPHORE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SETCC", PyInt_FromLong(XED_CATEGORY_SETCC));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SGX", PyInt_FromLong(XED_CATEGORY_SGX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SHA", PyInt_FromLong(XED_CATEGORY_SHA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SHIFT", PyInt_FromLong(XED_CATEGORY_SHIFT));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SMAP", PyInt_FromLong(XED_CATEGORY_SMAP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SSE", PyInt_FromLong(XED_CATEGORY_SSE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_STRINGOP", PyInt_FromLong(XED_CATEGORY_STRINGOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_STTNI", PyInt_FromLong(XED_CATEGORY_STTNI));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SYSCALL", PyInt_FromLong(XED_CATEGORY_SYSCALL));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SYSRET", PyInt_FromLong(XED_CATEGORY_SYSRET));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_SYSTEM", PyInt_FromLong(XED_CATEGORY_SYSTEM));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_TBM", PyInt_FromLong(XED_CATEGORY_TBM));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_UNCOND_BR", PyInt_FromLong(XED_CATEGORY_UNCOND_BR));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_VFMA", PyInt_FromLong(XED_CATEGORY_VFMA));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_VTX", PyInt_FromLong(XED_CATEGORY_VTX));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_WIDENOP", PyInt_FromLong(XED_CATEGORY_WIDENOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_X87_ALU", PyInt_FromLong(XED_CATEGORY_X87_ALU));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_XOP", PyInt_FromLong(XED_CATEGORY_XOP));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_XSAVE", PyInt_FromLong(XED_CATEGORY_XSAVE));
  PyDict_SetItemString(idOpcodeCategoryClassDict, "XED_CATEGORY_XSAVEOPT", PyInt_FromLong(XED_CATEGORY_XSAVEOPT));
}

