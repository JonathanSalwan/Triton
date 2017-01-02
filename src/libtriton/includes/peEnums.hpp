//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEENUMS_H
#define TRITON_PEENUMS_H



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Format namespace
  namespace format {
  /*!
   *  \ingroup triton
   *  \addtogroup format
   *  @{
   */

    //! The PE format namespace
    namespace pe {
    /*!
     *  \ingroup format
     *  \addtogroup pe
     *  @{
     */

      /*!
       *  \brief Some useful PE enums.
       */
      enum pe_e {
        PE_FORMAT_PE32                                  = 0x10b,
        PE_FORMAT_PE32PLUS                              = 0x20b,

        //Machine
        IMAGE_FILE_MACHINE_UNKNOWN                      = 0,
        IMAGE_FILE_MACHINE_AM33                         = 0x1d3,
        IMAGE_FILE_MACHINE_AMD64                        = 0x8664,
        IMAGE_FILE_MACHINE_ARM                          = 0x1c0,
        IMAGE_FILE_MACHINE_ARM64                        = 0xaa64,
        IMAGE_FILE_MACHINE_ARMNT                        = 0x1c4,
        IMAGE_FILE_MACHINE_EBC                          = 0xebc,
        IMAGE_FILE_MACHINE_I386                         = 0x14c,
        IMAGE_FILE_MACHINE_IA64                         = 0x200,
        IMAGE_FILE_MACHINE_M32R                         = 0x9041,
        IMAGE_FILE_MACHINE_MIPS16                       = 0x266,
        IMAGE_FILE_MACHINE_MIPSFPU                      = 0x366,
        IMAGE_FILE_MACHINE_MIPSFPU16                    = 0x466,
        IMAGE_FILE_MACHINE_POWERPC                      = 0x1f0,
        IMAGE_FILE_MACHINE_POWERPCFP                    = 0x1f1,
        IMAGE_FILE_MACHINE_R4000                        = 0x166,
        IMAGE_FILE_MACHINE_RISCV32                      = 0x5032,
        IMAGE_FILE_MACHINE_RISCV64                      = 0x5064,
        IMAGE_FILE_MACHINE_RISCV128                     = 0x5128,
        IMAGE_FILE_MACHINE_SH3                          = 0x1a2,
        IMAGE_FILE_MACHINE_SH3DSP                       = 0x1a3,
        IMAGE_FILE_MACHINE_SH4                          = 0x1a6,
        IMAGE_FILE_MACHINE_SH5                          = 0x1a8,
        IMAGE_FILE_MACHINE_THUMB                        = 0x1c2,
        IMAGE_FILE_MACHINE_WCEMIPSV2                    = 0x169,

        //Characteristic
        IMAGE_FILE_RELOCS_STRIPPED                      = 0x0001,
        IMAGE_FILE_EXECUTABLE_IMAGE                     = 0x0002,
        IMAGE_FILE_LINE_NUMS_STRIPPED                   = 0x0004,
        IMAGE_FILE_LOCAL_SYMS_STRIPPED                  = 0x0008,
        IMAGE_FILE_AGGRESSIVE_WS_TRIM                   = 0x0010,
        IMAGE_FILE_LARGE_ADDRESS_AWARE                  = 0x0020,
        IMAGE_FILE_BYTES_REVERSED_LO                    = 0x0080,
        IMAGE_FILE_32BIT_MACHINE                        = 0x0100,
        IMAGE_FILE_DEBUG_STRIPPED                       = 0x0200,
        IMAGE_FILE_REMOVABLE_RUN_FROM_SWAP              = 0x0400,
        IMAGE_FILE_NET_RUN_FROM_SWAP                    = 0x0800,
        IMAGE_FILE_SYSTEM                               = 0x1000,
        IMAGE_FILE_DLL                                  = 0x2000,
        IMAGE_FILE_UP_SYSTEM_ONLY                       = 0x4000,
        IMAGE_FILE_BYTES_REVERSED_HI                    = 0x8000,

        //Subsystem
        IMAGE_SUBSYSTEM_UNKNOWN                         = 0,
        IMAGE_SUBSYSTEM_NATIVE                          = 1,
        IMAGE_SUBSYSTEM_WINDOWS_GUI                     = 2,
        IMAGE_SUBSYSTEM_WINDOWS_CUI                     = 3,
        IMAGE_SUBSYSTEM_POSIX_CUI                       = 7,
        IMAGE_SUBSYSTEM_WINDOWS_CE_GUI                  = 9,
        IMAGE_SUBSYSTEM_EFI_APPLICATION                 = 10,
        IMAGE_SUBSYSTEM_EFI_BOOT_SERVICE_DRIVER         = 11,
        IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER              = 12,
        IMAGE_SUBSYSTEM_EFI_ROM                         = 13,
        IMAGE_SUBSYSTEM_XBOX                            = 14,

        //DLL characteristic
        IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA        = 0x0020,
        IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE           = 0x0040,
        IMAGE_DLLCHARACTERISTICS_FORCE_INTEGRITY        = 0x0080,
        IMAGE_DLLCHARACTERISTICS_NX_COMPAT              = 0x0100,
        IMAGE_DLLCHARACTERISTICS_NO_ISOLATION           = 0x0200,
        IMAGE_DLLCHARACTERISTICS_NO_SEH                 = 0x0400,
        IMAGE_DLLCHARACTERISTICS_NO_BIND                = 0x0800,
        IMAGE_DLLCHARACTERISTICS_APPCONTAINER           = 0x1000,
        IMAGE_DLLCHARACTERISTICS_WDM_DRIVER             = 0x2000,
        IMAGE_DLLCHARACTERISTICS_GUARD_CF               = 0x4000,
        IMAGE_DLLCHARACTERISTICS_TERMINAL_SERVER_AWARE  = 0x8000,


        IMAGE_SCN_TYPE_NO_PAD                           = 0x00000008,
        IMAGE_SCN_CNT_CODE                              = 0x00000020,
        IMAGE_SCN_CNT_INITIALIZED_DATA                  = 0x00000040,
        IMAGE_SCN_CNT_UNINITIALIZED_DATA                = 0x00000080,
        IMAGE_SCN_LNK_OTHER                             = 0x00000100,
        IMAGE_SCN_LNK_INFO                              = 0x00000200,
        IMAGE_SCN_LNK_REMOVE                            = 0x00000800,
        IMAGE_SCN_LNK_COMDAT                            = 0x00001000,
        IMAGE_SCN_GPREL                                 = 0x00008000,
        IMAGE_SCN_MEM_PURGEABLE                         = 0x00020000,
        IMAGE_SCN_MEM_16BIT                             = 0x00020000,
        IMAGE_SCN_MEM_LOCKED                            = 0x00040000,
        IMAGE_SCN_MEM_PRELOAD                           = 0x00080000,
        IMAGE_SCN_ALIGN_1BYTES                          = 0x00100000,
        IMAGE_SCN_ALIGN_2BYTES                          = 0x00200000,
        IMAGE_SCN_ALIGN_4BYTES                          = 0x00300000,
        IMAGE_SCN_ALIGN_8BYTES                          = 0x00400000,
        IMAGE_SCN_ALIGN_16BYTES                         = 0x00500000,
        IMAGE_SCN_ALIGN_32BYTES                         = 0x00600000,
        IMAGE_SCN_ALIGN_64BYTES                         = 0x00700000,
        IMAGE_SCN_ALIGN_128BYTES                        = 0x00800000,
        IMAGE_SCN_ALIGN_256BYTES                        = 0x00900000,
        IMAGE_SCN_ALIGN_512BYTES                        = 0x00A00000,
        IMAGE_SCN_ALIGN_1024BYTES                       = 0x00B00000,
        IMAGE_SCN_ALIGN_2048BYTES                       = 0x00C00000,
        IMAGE_SCN_ALIGN_4096BYTES                       = 0x00D00000,
        IMAGE_SCN_ALIGN_8192BYTES                       = 0x00E00000,
        IMAGE_SCN_LNK_NRELOC_OVFL                       = 0x01000000,
        IMAGE_SCN_MEM_DISCARDABLE                       = 0x02000000,
        IMAGE_SCN_MEM_NOT_CACHED                        = 0x04000000,
        IMAGE_SCN_MEM_NOT_PAGED                         = 0x08000000,
        IMAGE_SCN_MEM_SHARED                            = 0x10000000,
        IMAGE_SCN_MEM_EXECUTE                           = 0x20000000,
        IMAGE_SCN_MEM_READ                              = 0x40000000,
        IMAGE_SCN_MEM_WRITE                             = 0x80000000,
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEENUMS_H */
