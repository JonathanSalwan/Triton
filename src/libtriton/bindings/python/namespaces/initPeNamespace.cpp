//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/peEnums.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_PE_page PE
    \brief [**python api**] All information about the PE python namespace.

\tableofcontents

\section PE_py_description Description
<hr>

The PE namespace contains all enums used by the PE format.

\section PE_py_api Python API - Items of the PE namespace
<hr>

- **PE.PE_FORMAT_PE32**
- **PE.PE_FORMAT_PE32PLUS**
- **PE.IMAGE_FILE_MACHINE_UNKNOWN**
- **PE.IMAGE_FILE_MACHINE_AM33**
- **PE.IMAGE_FILE_MACHINE_AMD64**
- **PE.IMAGE_FILE_MACHINE_ARM**
- **PE.IMAGE_FILE_MACHINE_ARM64**
- **PE.IMAGE_FILE_MACHINE_ARMNT**
- **PE.IMAGE_FILE_MACHINE_EBC**
- **PE.IMAGE_FILE_MACHINE_I386**
- **PE.IMAGE_FILE_MACHINE_IA64**
- **PE.IMAGE_FILE_MACHINE_M32R**
- **PE.IMAGE_FILE_MACHINE_MIPS16**
- **PE.IMAGE_FILE_MACHINE_MIPSFPU**
- **PE.IMAGE_FILE_MACHINE_MIPSFPU16**
- **PE.IMAGE_FILE_MACHINE_POWERPC**
- **PE.IMAGE_FILE_MACHINE_POWERPCFP**
- **PE.IMAGE_FILE_MACHINE_R4000**
- **PE.IMAGE_FILE_MACHINE_RISCV32**
- **PE.IMAGE_FILE_MACHINE_RISCV64**
- **PE.IMAGE_FILE_MACHINE_RISCV128**
- **PE.IMAGE_FILE_MACHINE_SH3**
- **PE.IMAGE_FILE_MACHINE_SH3DSP**
- **PE.IMAGE_FILE_MACHINE_SH4**
- **PE.IMAGE_FILE_MACHINE_SH5**
- **PE.IMAGE_FILE_MACHINE_THUMB**
- **PE.IMAGE_FILE_MACHINE_WCEMIPSV2**
- **PE.IMAGE_FILE_RELOCS_STRIPPED**
- **PE.IMAGE_FILE_EXECUTABLE_IMAGE**
- **PE.IMAGE_FILE_LINE_NUMS_STRIPPED**
- **PE.IMAGE_FILE_LOCAL_SYMS_STRIPPED**
- **PE.IMAGE_FILE_AGGRESSIVE_WS_TRIM**
- **PE.IMAGE_FILE_LARGE_ADDRESS_AWARE**
- **PE.IMAGE_FILE_BYTES_REVERSED_LO**
- **PE.IMAGE_FILE_32BIT_MACHINE**
- **PE.IMAGE_FILE_DEBUG_STRIPPED**
- **PE.IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP**
- **PE.IMAGE_FILE_NET_RUN_FROM_SWAP**
- **PE.IMAGE_FILE_SYSTEM**
- **PE.IMAGE_FILE_DLL**
- **PE.IMAGE_FILE_UP_SYSTEM_ONLY**
- **PE.IMAGE_FILE_BYTES_REVERSED_HI**
- **PE.IMAGE_SUBSYSTEM_UNKNOWN**
- **PE.IMAGE_SUBSYSTEM_NATIVE**
- **PE.IMAGE_SUBSYSTEM_WINDOWS_GUI**
- **PE.IMAGE_SUBSYSTEM_WINDOWS_CUI**
- **PE.IMAGE_SUBSYSTEM_POSIX_CUI**
- **PE.IMAGE_SUBSYSTEM_WINDOWS_CE_GUI**
- **PE.IMAGE_SUBSYSTEM_EFI_APPLICATION**
- **PE.IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER**
- **PE.IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER**
- **PE.IMAGE_SUBSYSTEM_EFI_ROM**
- **PE.IMAGE_SUBSYSTEM_XBOX**
- **PE.IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA**
- **PE.IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE**
- **PE.IMAGE_DLLCHARACTERISTICS_FORCE_INTEGRITY**
- **PE.IMAGE_DLLCHARACTERISTICS_NX_COMPAT**
- **PE.IMAGE_DLLCHARACTERISTICS_NO_ISOLATION**
- **PE.IMAGE_DLLCHARACTERISTICS_NO_SEH**
- **PE.IMAGE_DLLCHARACTERISTICS_NO_BIND**
- **PE.IMAGE_DLLCHARACTERISTICS_APPCONTAINER**
- **PE.IMAGE_DLLCHARACTERISTICS_WDM_DRIVER**
- **PE.IMAGE_DLLCHARACTERISTICS_GUARD_CF**
- **PE.IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE**
- **PE.IMAGE_SCN_TYPE_NO_PAD**
- **PE.IMAGE_SCN_CNT_CODE**
- **PE.IMAGE_SCN_CNT_INITIALIZED_DATA**
- **PE.IMAGE_SCN_CNT_UNINITIALIZED_DATA**
- **PE.IMAGE_SCN_LNK_OTHER**
- **PE.IMAGE_SCN_LNK_INFO**
- **PE.IMAGE_SCN_LNK_REMOVE**
- **PE.IMAGE_SCN_LNK_COMDAT**
- **PE.IMAGE_SCN_GPREL**
- **PE.IMAGE_SCN_MEM_PURGEABLE**
- **PE.IMAGE_SCN_MEM_16BIT**
- **PE.IMAGE_SCN_MEM_LOCKED**
- **PE.IMAGE_SCN_MEM_PRELOAD**
- **PE.IMAGE_SCN_ALIGN_1BYTES**
- **PE.IMAGE_SCN_ALIGN_2BYTES**
- **PE.IMAGE_SCN_ALIGN_4BYTES**
- **PE.IMAGE_SCN_ALIGN_8BYTES**
- **PE.IMAGE_SCN_ALIGN_16BYTES**
- **PE.IMAGE_SCN_ALIGN_32BYTES**
- **PE.IMAGE_SCN_ALIGN_64BYTES**
- **PE.IMAGE_SCN_ALIGN_128BYTES**
- **PE.IMAGE_SCN_ALIGN_256BYTES**
- **PE.IMAGE_SCN_ALIGN_512BYTES**
- **PE.IMAGE_SCN_ALIGN_1024BYTES**
- **PE.IMAGE_SCN_ALIGN_2048BYTES**
- **PE.IMAGE_SCN_ALIGN_4096BYTES**
- **PE.IMAGE_SCN_ALIGN_8192BYTES**
- **PE.IMAGE_SCN_LNK_NRELOC_OVFL**
- **PE.IMAGE_SCN_MEM_DISCARDABLE**
- **PE.IMAGE_SCN_MEM_NOT_CACHED**
- **PE.IMAGE_SCN_MEM_NOT_PAGED**
- **PE.IMAGE_SCN_MEM_SHARED**
- **PE.IMAGE_SCN_MEM_EXECUTE**
- **PE.IMAGE_SCN_MEM_READ**
- **PE.IMAGE_SCN_MEM_WRITE**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initPENamespace(PyObject* peDict) {
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_AMD64",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_AMD64));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_I386",                             PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_I386));
        PyDict_SetItemString(peDict, "PE_FORMAT_PE32",                                      PyLong_FromUint32(triton::format::pe::PE_FORMAT_PE32));
        PyDict_SetItemString(peDict, "PE_FORMAT_PE32PLUS",                                  PyLong_FromUint32(triton::format::pe::PE_FORMAT_PE32PLUS));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_UNKNOWN",                          PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_UNKNOWN));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_AM33",                             PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_AM33));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_AMD64",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_AMD64));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_ARM",                              PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_ARM));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_ARM64",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_ARM64));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_ARMNT",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_ARMNT));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_EBC",                              PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_EBC));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_I386",                             PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_I386));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_IA64",                             PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_IA64));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_M32R",                             PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_M32R));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_MIPS16",                           PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_MIPS16));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_MIPSFPU",                          PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_MIPSFPU));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_MIPSFPU16",                        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_MIPSFPU16));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_POWERPC",                          PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_POWERPC));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_POWERPCFP",                        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_POWERPCFP));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_R4000",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_R4000));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_RISCV32",                          PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_RISCV32));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_RISCV64",                          PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_RISCV64));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_RISCV128",                         PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_RISCV128));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_SH3",                              PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_SH3));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_SH3DSP",                           PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_SH3DSP));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_SH4",                              PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_SH4));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_SH5",                              PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_SH5));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_THUMB",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_THUMB));
        PyDict_SetItemString(peDict, "IMAGE_FILE_MACHINE_WCEMIPSV2",                        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_MACHINE_WCEMIPSV2));
        PyDict_SetItemString(peDict, "IMAGE_FILE_RELOCS_STRIPPED",                          PyLong_FromUint32(triton::format::pe::IMAGE_FILE_RELOCS_STRIPPED));
        PyDict_SetItemString(peDict, "IMAGE_FILE_EXECUTABLE_IMAGE",                         PyLong_FromUint32(triton::format::pe::IMAGE_FILE_EXECUTABLE_IMAGE));
        PyDict_SetItemString(peDict, "IMAGE_FILE_LINE_NUMS_STRIPPED",                       PyLong_FromUint32(triton::format::pe::IMAGE_FILE_LINE_NUMS_STRIPPED));
        PyDict_SetItemString(peDict, "IMAGE_FILE_LOCAL_SYMS_STRIPPED",                      PyLong_FromUint32(triton::format::pe::IMAGE_FILE_LOCAL_SYMS_STRIPPED));
        PyDict_SetItemString(peDict, "IMAGE_FILE_AGGRESSIVE_WS_TRIM",                       PyLong_FromUint32(triton::format::pe::IMAGE_FILE_AGGRESSIVE_WS_TRIM));
        PyDict_SetItemString(peDict, "IMAGE_FILE_LARGE_ADDRESS_AWARE",                      PyLong_FromUint32(triton::format::pe::IMAGE_FILE_LARGE_ADDRESS_AWARE));
        PyDict_SetItemString(peDict, "IMAGE_FILE_BYTES_REVERSED_LO",                        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_BYTES_REVERSED_LO));
        PyDict_SetItemString(peDict, "IMAGE_FILE_32BIT_MACHINE",                            PyLong_FromUint32(triton::format::pe::IMAGE_FILE_32BIT_MACHINE));
        PyDict_SetItemString(peDict, "IMAGE_FILE_DEBUG_STRIPPED",                           PyLong_FromUint32(triton::format::pe::IMAGE_FILE_DEBUG_STRIPPED));
        PyDict_SetItemString(peDict, "IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP",                  PyLong_FromUint32(triton::format::pe::IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP));
        PyDict_SetItemString(peDict, "IMAGE_FILE_NET_RUN_FROM_SWAP",                        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_NET_RUN_FROM_SWAP));
        PyDict_SetItemString(peDict, "IMAGE_FILE_SYSTEM",                                   PyLong_FromUint32(triton::format::pe::IMAGE_FILE_SYSTEM));
        PyDict_SetItemString(peDict, "IMAGE_FILE_DLL",                                      PyLong_FromUint32(triton::format::pe::IMAGE_FILE_DLL));
        PyDict_SetItemString(peDict, "IMAGE_FILE_UP_SYSTEM_ONLY",                           PyLong_FromUint32(triton::format::pe::IMAGE_FILE_UP_SYSTEM_ONLY));
        PyDict_SetItemString(peDict, "IMAGE_FILE_BYTES_REVERSED_HI",                        PyLong_FromUint32(triton::format::pe::IMAGE_FILE_BYTES_REVERSED_HI));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_UNKNOWN",                             PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_UNKNOWN));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_NATIVE",                              PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_NATIVE));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_WINDOWS_GUI",                         PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_WINDOWS_GUI));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_WINDOWS_CUI",                         PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_WINDOWS_CUI));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_POSIX_CUI",                           PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_POSIX_CUI));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_WINDOWS_CE_GUI",                      PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_WINDOWS_CE_GUI));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_EFI_APPLICATION",                     PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_EFI_APPLICATION));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER",             PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER",                  PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_EFI_ROM",                             PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_EFI_ROM));
        PyDict_SetItemString(peDict, "IMAGE_SUBSYSTEM_XBOX",                                PyLong_FromUint32(triton::format::pe::IMAGE_SUBSYSTEM_XBOX));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA",            PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE",               PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_FORCE_INTEGRITY",            PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_FORCE_INTEGRITY));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_NX_COMPAT",                  PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_NX_COMPAT));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_NO_ISOLATION",               PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_NO_ISOLATION));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_NO_SEH",                     PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_NO_SEH));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_NO_BIND",                    PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_NO_BIND));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_APPCONTAINER",               PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_APPCONTAINER));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_WDM_DRIVER",                 PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_WDM_DRIVER));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_GUARD_CF",                   PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_GUARD_CF));
        PyDict_SetItemString(peDict, "IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE",      PyLong_FromUint32(triton::format::pe::IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE));
        PyDict_SetItemString(peDict, "IMAGE_SCN_TYPE_NO_PAD",                               PyLong_FromUint32(triton::format::pe::IMAGE_SCN_TYPE_NO_PAD));
        PyDict_SetItemString(peDict, "IMAGE_SCN_CNT_CODE",                                  PyLong_FromUint32(triton::format::pe::IMAGE_SCN_CNT_CODE));
        PyDict_SetItemString(peDict, "IMAGE_SCN_CNT_INITIALIZED_DATA",                      PyLong_FromUint32(triton::format::pe::IMAGE_SCN_CNT_INITIALIZED_DATA));
        PyDict_SetItemString(peDict, "IMAGE_SCN_CNT_UNINITIALIZED_DATA",                    PyLong_FromUint32(triton::format::pe::IMAGE_SCN_CNT_UNINITIALIZED_DATA));
        PyDict_SetItemString(peDict, "IMAGE_SCN_LNK_OTHER",                                 PyLong_FromUint32(triton::format::pe::IMAGE_SCN_LNK_OTHER));
        PyDict_SetItemString(peDict, "IMAGE_SCN_LNK_INFO",                                  PyLong_FromUint32(triton::format::pe::IMAGE_SCN_LNK_INFO));
        PyDict_SetItemString(peDict, "IMAGE_SCN_LNK_REMOVE",                                PyLong_FromUint32(triton::format::pe::IMAGE_SCN_LNK_REMOVE));
        PyDict_SetItemString(peDict, "IMAGE_SCN_LNK_COMDAT",                                PyLong_FromUint32(triton::format::pe::IMAGE_SCN_LNK_COMDAT));
        PyDict_SetItemString(peDict, "IMAGE_SCN_GPREL",                                     PyLong_FromUint32(triton::format::pe::IMAGE_SCN_GPREL));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_PURGEABLE",                             PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_PURGEABLE));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_16BIT",                                 PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_16BIT));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_LOCKED",                                PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_LOCKED));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_PRELOAD",                               PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_PRELOAD));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_1BYTES",                              PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_1BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_2BYTES",                              PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_2BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_4BYTES",                              PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_4BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_8BYTES",                              PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_8BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_16BYTES",                             PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_16BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_32BYTES",                             PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_32BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_64BYTES",                             PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_64BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_128BYTES",                            PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_128BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_256BYTES",                            PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_256BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_512BYTES",                            PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_512BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_1024BYTES",                           PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_1024BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_2048BYTES",                           PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_2048BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_4096BYTES",                           PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_4096BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_ALIGN_8192BYTES",                           PyLong_FromUint32(triton::format::pe::IMAGE_SCN_ALIGN_8192BYTES));
        PyDict_SetItemString(peDict, "IMAGE_SCN_LNK_NRELOC_OVFL",                           PyLong_FromUint32(triton::format::pe::IMAGE_SCN_LNK_NRELOC_OVFL));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_DISCARDABLE",                           PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_DISCARDABLE));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_NOT_CACHED",                            PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_NOT_CACHED));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_NOT_PAGED",                             PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_NOT_PAGED));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_SHARED",                                PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_SHARED));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_EXECUTE",                               PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_EXECUTE));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_READ",                                  PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_READ));
        PyDict_SetItemString(peDict, "IMAGE_SCN_MEM_WRITE",                                 PyLong_FromUint32(triton::format::pe::IMAGE_SCN_MEM_WRITE));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
