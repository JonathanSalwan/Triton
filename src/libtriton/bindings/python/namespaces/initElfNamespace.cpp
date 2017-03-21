//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/elfEnums.hpp>
#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>



/*! \page py_ELF_page ELF
    \brief [**python api**] All information about the ELF python namespace.

\tableofcontents

\section ELF_py_description Description
<hr>

The ELF namespace contains all enums used by the ELF format.

\section ELF_py_api Python API - Items of the ELF namespace
<hr>

- **ELF.EI_NIDENT**
- **ELF.ELFCLASSNONE**
- **ELF.ELFCLASS32**
- **ELF.ELFCLASS64**
- **ELF.ELFDATANONE**
- **ELF.ELFDATA2LSB**
- **ELF.ELFDATA2MSB**
- **ELF.PF_X**
- **ELF.PF_W**
- **ELF.PF_R**
- **ELF.PT_NULL**
- **ELF.PT_LOAD**
- **ELF.PT_DYNAMIC**
- **ELF.PT_INTERP**
- **ELF.PT_NOTE**
- **ELF.PT_SHLIB**
- **ELF.PT_PHDR**
- **ELF.PT_GNU_EH_FRAME**
- **ELF.PT_GNU_STACK**
- **ELF.PT_GNU_RELRO**
- **ELF.PT_LOPROC**
- **ELF.PT_HIPROC**
- **ELF.SHN_UNDEF**
- **ELF.SHN_XINDEX**
- **ELF.SHF_WRITE**
- **ELF.SHF_ALLOC**
- **ELF.SHF_EXECINSTR**
- **ELF.SHF_MASKPROC**
- **ELF.SHT_NULL**
- **ELF.SHT_PROGBITS**
- **ELF.SHT_SYMTAB**
- **ELF.SHT_STRTAB**
- **ELF.SHT_RELA**
- **ELF.SHT_HASH**
- **ELF.SHT_DYNAMIC**
- **ELF.SHT_NOTE**
- **ELF.SHT_NOBITS**
- **ELF.SHT_REL**
- **ELF.SHT_SHLIB**
- **ELF.SHT_DYNSYM**
- **ELF.SHT_SYMTAB_SHNDX**
- **ELF.SHT_LOPROC**
- **ELF.SHT_HIPROC**
- **ELF.SHT_LOUSER**
- **ELF.SHT_HIUSER**
- **ELF.DT_NULL**
- **ELF.DT_NEEDED**
- **ELF.DT_PLTRELSZ**
- **ELF.DT_PLTGOT**
- **ELF.DT_HASH**
- **ELF.DT_STRTAB**
- **ELF.DT_SYMTAB**
- **ELF.DT_RELA**
- **ELF.DT_RELASZ**
- **ELF.DT_RELAENT**
- **ELF.DT_STRSZ**
- **ELF.DT_SYMENT**
- **ELF.DT_INIT**
- **ELF.DT_FINI**
- **ELF.DT_SONAME**
- **ELF.DT_RPATH**
- **ELF.DT_SYMBOLIC**
- **ELF.DT_REL**
- **ELF.DT_RELSZ**
- **ELF.DT_RELENT**
- **ELF.DT_PLTREL**
- **ELF.DT_DEBUG**
- **ELF.DT_TEXTREL**
- **ELF.DT_JMPREL**
- **ELF.DT_BIND_NOW**
- **ELF.DT_INIT_ARRAY**
- **ELF.DT_FINI_ARRAY**
- **ELF.DT_INIT_ARRAYSZ**
- **ELF.DT_FINI_ARRAYSZ**
- **ELF.DT_RUNPATH**
- **ELF.DT_GNU_HASH**
- **ELF.DT_VERSYM**
- **ELF.DT_VERDEF**
- **ELF.DT_VERDEFNUM**
- **ELF.DT_VERNEED**
- **ELF.DT_VERNEEDNUM**
- **ELF.STV_DEFAULT**
- **ELF.STV_INTERNAL**
- **ELF.STV_HIDDEN**
- **ELF.STV_PROTECTED**

*/



namespace triton {
  namespace bindings {
    namespace python {

      void initElfNamespace(PyObject* elfDict) {
        PyDict_SetItemString(elfDict, "EI_NIDENT",        PyLong_FromUint32(triton::format::elf::EI_NIDENT));
        PyDict_SetItemString(elfDict, "ELFCLASSNONE",     PyLong_FromUint32(triton::format::elf::ELFCLASSNONE));
        PyDict_SetItemString(elfDict, "ELFCLASS32",       PyLong_FromUint32(triton::format::elf::ELFCLASS32));
        PyDict_SetItemString(elfDict, "ELFCLASS64",       PyLong_FromUint32(triton::format::elf::ELFCLASS64));
        PyDict_SetItemString(elfDict, "ELFDATANONE",      PyLong_FromUint32(triton::format::elf::ELFDATANONE));
        PyDict_SetItemString(elfDict, "ELFDATA2LSB",      PyLong_FromUint32(triton::format::elf::ELFDATA2LSB));
        PyDict_SetItemString(elfDict, "ELFDATA2MSB",      PyLong_FromUint32(triton::format::elf::ELFDATA2MSB));
        PyDict_SetItemString(elfDict, "PF_X",             PyLong_FromUint32(triton::format::elf::PF_X));
        PyDict_SetItemString(elfDict, "PF_W",             PyLong_FromUint32(triton::format::elf::PF_W));
        PyDict_SetItemString(elfDict, "PF_R",             PyLong_FromUint32(triton::format::elf::PF_R));
        PyDict_SetItemString(elfDict, "PT_NULL",          PyLong_FromUint32(triton::format::elf::PT_NULL));
        PyDict_SetItemString(elfDict, "PT_LOAD",          PyLong_FromUint32(triton::format::elf::PT_LOAD));
        PyDict_SetItemString(elfDict, "PT_DYNAMIC",       PyLong_FromUint32(triton::format::elf::PT_DYNAMIC));
        PyDict_SetItemString(elfDict, "PT_INTERP",        PyLong_FromUint32(triton::format::elf::PT_INTERP));
        PyDict_SetItemString(elfDict, "PT_NOTE",          PyLong_FromUint32(triton::format::elf::PT_NOTE));
        PyDict_SetItemString(elfDict, "PT_SHLIB",         PyLong_FromUint32(triton::format::elf::PT_SHLIB));
        PyDict_SetItemString(elfDict, "PT_PHDR",          PyLong_FromUint32(triton::format::elf::PT_PHDR));
        PyDict_SetItemString(elfDict, "PT_GNU_EH_FRAME",  PyLong_FromUint32(triton::format::elf::PT_GNU_EH_FRAME));
        PyDict_SetItemString(elfDict, "PT_GNU_STACK",     PyLong_FromUint32(triton::format::elf::PT_GNU_STACK));
        PyDict_SetItemString(elfDict, "PT_GNU_RELRO",     PyLong_FromUint32(triton::format::elf::PT_GNU_RELRO));
        PyDict_SetItemString(elfDict, "PT_LOPROC",        PyLong_FromUint32(triton::format::elf::PT_LOPROC));
        PyDict_SetItemString(elfDict, "PT_HIPROC",        PyLong_FromUint32(triton::format::elf::PT_HIPROC));
        PyDict_SetItemString(elfDict, "SHN_UNDEF",        PyLong_FromUint32(triton::format::elf::SHN_UNDEF));
        PyDict_SetItemString(elfDict, "SHN_XINDEX",       PyLong_FromUint32(triton::format::elf::SHN_XINDEX));
        PyDict_SetItemString(elfDict, "SHF_WRITE",        PyLong_FromUint32(triton::format::elf::SHF_WRITE));
        PyDict_SetItemString(elfDict, "SHF_ALLOC",        PyLong_FromUint32(triton::format::elf::SHF_ALLOC));
        PyDict_SetItemString(elfDict, "SHF_EXECINSTR",    PyLong_FromUint32(triton::format::elf::SHF_EXECINSTR));
        PyDict_SetItemString(elfDict, "SHF_MASKPROC",     PyLong_FromUint32(triton::format::elf::SHF_MASKPROC));
        PyDict_SetItemString(elfDict, "SHT_NULL",         PyLong_FromUint32(triton::format::elf::SHT_NULL));
        PyDict_SetItemString(elfDict, "SHT_PROGBITS",     PyLong_FromUint32(triton::format::elf::SHT_PROGBITS));
        PyDict_SetItemString(elfDict, "SHT_SYMTAB",       PyLong_FromUint32(triton::format::elf::SHT_SYMTAB));
        PyDict_SetItemString(elfDict, "SHT_STRTAB",       PyLong_FromUint32(triton::format::elf::SHT_STRTAB));
        PyDict_SetItemString(elfDict, "SHT_RELA",         PyLong_FromUint32(triton::format::elf::SHT_RELA));
        PyDict_SetItemString(elfDict, "SHT_HASH",         PyLong_FromUint32(triton::format::elf::SHT_HASH));
        PyDict_SetItemString(elfDict, "SHT_DYNAMIC",      PyLong_FromUint32(triton::format::elf::SHT_DYNAMIC));
        PyDict_SetItemString(elfDict, "SHT_NOTE",         PyLong_FromUint32(triton::format::elf::SHT_NOTE));
        PyDict_SetItemString(elfDict, "SHT_NOBITS",       PyLong_FromUint32(triton::format::elf::SHT_NOBITS));
        PyDict_SetItemString(elfDict, "SHT_REL",          PyLong_FromUint32(triton::format::elf::SHT_REL));
        PyDict_SetItemString(elfDict, "SHT_SHLIB",        PyLong_FromUint32(triton::format::elf::SHT_SHLIB));
        PyDict_SetItemString(elfDict, "SHT_DYNSYM",       PyLong_FromUint32(triton::format::elf::SHT_DYNSYM));
        PyDict_SetItemString(elfDict, "SHT_SYMTAB_SHNDX", PyLong_FromUint32(triton::format::elf::SHT_SYMTAB_SHNDX));
        PyDict_SetItemString(elfDict, "SHT_LOPROC",       PyLong_FromUint32(triton::format::elf::SHT_LOPROC));
        PyDict_SetItemString(elfDict, "SHT_HIPROC",       PyLong_FromUint32(triton::format::elf::SHT_HIPROC));
        PyDict_SetItemString(elfDict, "SHT_LOUSER",       PyLong_FromUint32(triton::format::elf::SHT_LOUSER));
        PyDict_SetItemString(elfDict, "SHT_HIUSER",       PyLong_FromUint32(triton::format::elf::SHT_HIUSER));
        PyDict_SetItemString(elfDict, "DT_NULL",          PyLong_FromUint32(triton::format::elf::DT_NULL));
        PyDict_SetItemString(elfDict, "DT_NEEDED",        PyLong_FromUint32(triton::format::elf::DT_NEEDED));
        PyDict_SetItemString(elfDict, "DT_PLTRELSZ",      PyLong_FromUint32(triton::format::elf::DT_PLTRELSZ));
        PyDict_SetItemString(elfDict, "DT_PLTGOT",        PyLong_FromUint32(triton::format::elf::DT_PLTGOT));
        PyDict_SetItemString(elfDict, "DT_HASH",          PyLong_FromUint32(triton::format::elf::DT_HASH));
        PyDict_SetItemString(elfDict, "DT_STRTAB",        PyLong_FromUint32(triton::format::elf::DT_STRTAB));
        PyDict_SetItemString(elfDict, "DT_SYMTAB",        PyLong_FromUint32(triton::format::elf::DT_SYMTAB));
        PyDict_SetItemString(elfDict, "DT_RELA",          PyLong_FromUint32(triton::format::elf::DT_RELA));
        PyDict_SetItemString(elfDict, "DT_RELASZ",        PyLong_FromUint32(triton::format::elf::DT_RELASZ));
        PyDict_SetItemString(elfDict, "DT_RELAENT",       PyLong_FromUint32(triton::format::elf::DT_RELAENT));
        PyDict_SetItemString(elfDict, "DT_STRSZ",         PyLong_FromUint32(triton::format::elf::DT_STRSZ));
        PyDict_SetItemString(elfDict, "DT_SYMENT",        PyLong_FromUint32(triton::format::elf::DT_SYMENT));
        PyDict_SetItemString(elfDict, "DT_INIT",          PyLong_FromUint32(triton::format::elf::DT_INIT));
        PyDict_SetItemString(elfDict, "DT_FINI",          PyLong_FromUint32(triton::format::elf::DT_FINI));
        PyDict_SetItemString(elfDict, "DT_SONAME",        PyLong_FromUint32(triton::format::elf::DT_SONAME));
        PyDict_SetItemString(elfDict, "DT_RPATH",         PyLong_FromUint32(triton::format::elf::DT_RPATH));
        PyDict_SetItemString(elfDict, "DT_SYMBOLIC",      PyLong_FromUint32(triton::format::elf::DT_SYMBOLIC));
        PyDict_SetItemString(elfDict, "DT_REL",           PyLong_FromUint32(triton::format::elf::DT_REL));
        PyDict_SetItemString(elfDict, "DT_RELSZ",         PyLong_FromUint32(triton::format::elf::DT_RELSZ));
        PyDict_SetItemString(elfDict, "DT_RELENT",        PyLong_FromUint32(triton::format::elf::DT_RELENT));
        PyDict_SetItemString(elfDict, "DT_PLTREL",        PyLong_FromUint32(triton::format::elf::DT_PLTREL));
        PyDict_SetItemString(elfDict, "DT_DEBUG",         PyLong_FromUint32(triton::format::elf::DT_DEBUG));
        PyDict_SetItemString(elfDict, "DT_TEXTREL",       PyLong_FromUint32(triton::format::elf::DT_TEXTREL));
        PyDict_SetItemString(elfDict, "DT_JMPREL",        PyLong_FromUint32(triton::format::elf::DT_JMPREL));
        PyDict_SetItemString(elfDict, "DT_BIND_NOW",      PyLong_FromUint32(triton::format::elf::DT_BIND_NOW));
        PyDict_SetItemString(elfDict, "DT_INIT_ARRAY",    PyLong_FromUint32(triton::format::elf::DT_INIT_ARRAY));
        PyDict_SetItemString(elfDict, "DT_FINI_ARRAY",    PyLong_FromUint32(triton::format::elf::DT_FINI_ARRAY));
        PyDict_SetItemString(elfDict, "DT_INIT_ARRAYSZ",  PyLong_FromUint32(triton::format::elf::DT_INIT_ARRAYSZ));
        PyDict_SetItemString(elfDict, "DT_FINI_ARRAYSZ",  PyLong_FromUint32(triton::format::elf::DT_FINI_ARRAYSZ));
        PyDict_SetItemString(elfDict, "DT_RUNPATH",       PyLong_FromUint32(triton::format::elf::DT_RUNPATH));
        PyDict_SetItemString(elfDict, "DT_GNU_HASH",      PyLong_FromUint32(triton::format::elf::DT_GNU_HASH));
        PyDict_SetItemString(elfDict, "DT_VERSYM",        PyLong_FromUint32(triton::format::elf::DT_VERSYM));
        PyDict_SetItemString(elfDict, "DT_VERDEF",        PyLong_FromUint32(triton::format::elf::DT_VERDEF));
        PyDict_SetItemString(elfDict, "DT_VERDEFNUM",     PyLong_FromUint32(triton::format::elf::DT_VERDEFNUM));
        PyDict_SetItemString(elfDict, "DT_VERNEED",       PyLong_FromUint32(triton::format::elf::DT_VERNEED));
        PyDict_SetItemString(elfDict, "DT_VERNEEDNUM",    PyLong_FromUint32(triton::format::elf::DT_VERNEEDNUM));
        PyDict_SetItemString(elfDict, "STV_DEFAULT",      PyLong_FromUint32(triton::format::elf::STV_DEFAULT));
        PyDict_SetItemString(elfDict, "STV_INTERNAL",     PyLong_FromUint32(triton::format::elf::STV_INTERNAL));
        PyDict_SetItemString(elfDict, "STV_HIDDEN",       PyLong_FromUint32(triton::format::elf::STV_HIDDEN));
        PyDict_SetItemString(elfDict, "STV_PROTECTED",    PyLong_FromUint32(triton::format::elf::STV_PROTECTED));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
