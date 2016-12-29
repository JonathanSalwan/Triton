//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <peDataDirectory.hpp>
#include <exceptions.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeDataDirectory::PeDataDirectory() {
        this->exportTable_rva = 0;
        this->exportTable_size = 0;
        this->importTable_rva = 0;
        this->importTable_size = 0;
        this->resourceTable_rva = 0;
        this->resourceTable_size = 0;
        this->exceptionTable_rva = 0;
        this->exceptionTable_size = 0;
        this->certificateTable_rva = 0;
        this->certificateTable_size = 0;
        this->baseRelocationTable_rva = 0;
        this->baseRelocationTable_size = 0;
        this->debugTable_rva = 0;
        this->debugTable_size = 0;
        this->architectureTable_rva = 0;
        this->architectureTable_size = 0;
        this->globalPtr_rva = 0;
        this->globalPtr_size = 0;
        this->tlsTable_rva = 0;
        this->tlsTable_size = 0;
        this->loadConfigTable_rva = 0;
        this->loadConfigTable_size = 0;
        this->boundImportTable_rva = 0;
        this->boundImportTable_size = 0;
        this->importAddressTable_rva = 0;
        this->importAddressTable_size = 0;
        this->delayImportDescriptor_rva = 0;
        this->delayImportDescriptor_size = 0;
        this->clrRuntimeHeader_rva = 0;
        this->clrRuntimeHeader_size = 0;
        this->reserved = 0;
      }


      PeDataDirectory::PeDataDirectory(const PeDataDirectory& copy) {
        this->exportTable_rva            = copy.exportTable_rva;
        this->exportTable_size           = copy.exportTable_size;
        this->importTable_rva            = copy.importTable_rva;
        this->importTable_size           = copy.importTable_size;
        this->resourceTable_rva          = copy.resourceTable_rva;
        this->resourceTable_size         = copy.resourceTable_size;
        this->exceptionTable_rva         = copy.exceptionTable_rva;
        this->exceptionTable_size        = copy.exceptionTable_size;
        this->certificateTable_rva       = copy.certificateTable_rva;
        this->certificateTable_size      = copy.certificateTable_size;
        this->baseRelocationTable_rva    = copy.baseRelocationTable_rva;
        this->baseRelocationTable_size   = copy.baseRelocationTable_size;
        this->debugTable_rva             = copy.debugTable_rva;
        this->debugTable_size            = copy.debugTable_size;
        this->architectureTable_rva      = copy.architectureTable_rva;
        this->architectureTable_size     = copy.architectureTable_size;
        this->globalPtr_rva              = copy.globalPtr_rva;
        this->globalPtr_size             = copy.globalPtr_size;
        this->tlsTable_rva               = copy.tlsTable_rva;
        this->tlsTable_size              = copy.tlsTable_size;
        this->loadConfigTable_rva        = copy.loadConfigTable_rva;
        this->loadConfigTable_size       = copy.loadConfigTable_size;
        this->boundImportTable_rva       = copy.boundImportTable_rva;
        this->boundImportTable_size      = copy.boundImportTable_size;
        this->importAddressTable_rva     = copy.importAddressTable_rva;
        this->importAddressTable_size    = copy.importAddressTable_size;
        this->delayImportDescriptor_rva  = copy.delayImportDescriptor_rva;
        this->delayImportDescriptor_size = copy.delayImportDescriptor_size;
        this->clrRuntimeHeader_rva       = copy.clrRuntimeHeader_rva;
        this->clrRuntimeHeader_size      = copy.clrRuntimeHeader_size;
        this->reserved                   = copy.reserved;
      }


      PeDataDirectory::~PeDataDirectory() {
      }


      PeDataDirectory &PeDataDirectory::operator=(const PeDataDirectory& copy) {
        if (this == &copy)
            return *this;
        this->exportTable_rva            = copy.exportTable_rva;
        this->exportTable_size           = copy.exportTable_size;
        this->importTable_rva            = copy.importTable_rva;
        this->importTable_size           = copy.importTable_size;
        this->resourceTable_rva          = copy.resourceTable_rva;
        this->resourceTable_size         = copy.resourceTable_size;
        this->exceptionTable_rva         = copy.exceptionTable_rva;
        this->exceptionTable_size        = copy.exceptionTable_size;
        this->certificateTable_rva       = copy.certificateTable_rva;
        this->certificateTable_size      = copy.certificateTable_size;
        this->baseRelocationTable_rva    = copy.baseRelocationTable_rva;
        this->baseRelocationTable_size   = copy.baseRelocationTable_size;
        this->debugTable_rva             = copy.debugTable_rva;
        this->debugTable_size            = copy.debugTable_size;
        this->architectureTable_rva      = copy.architectureTable_rva;
        this->architectureTable_size     = copy.architectureTable_size;
        this->globalPtr_rva              = copy.globalPtr_rva;
        this->globalPtr_size             = copy.globalPtr_size;
        this->tlsTable_rva               = copy.tlsTable_rva;
        this->tlsTable_size              = copy.tlsTable_size;
        this->loadConfigTable_rva        = copy.loadConfigTable_rva;
        this->loadConfigTable_size       = copy.loadConfigTable_size;
        this->boundImportTable_rva       = copy.boundImportTable_rva;
        this->boundImportTable_size      = copy.boundImportTable_size;
        this->importAddressTable_rva     = copy.importAddressTable_rva;
        this->importAddressTable_size    = copy.importAddressTable_size;
        this->delayImportDescriptor_rva  = copy.delayImportDescriptor_rva;
        this->delayImportDescriptor_size = copy.delayImportDescriptor_size;
        this->clrRuntimeHeader_rva       = copy.clrRuntimeHeader_rva;
        this->clrRuntimeHeader_size      = copy.clrRuntimeHeader_size;
        this->reserved                   = copy.reserved;
        return *this;
      }

      void PeDataDirectory::parse(const triton::uint8* raw) {
        std::memcpy(&exportTable_rva, raw, 128);
      }

      triton::uint32 PeDataDirectory::getExportTable_rva(void) const {
        return this->exportTable_rva;
      }


      triton::uint32 PeDataDirectory::getExportTable_size(void) const {
        return this->exportTable_size;
      }


      triton::uint32 PeDataDirectory::getImportTable_rva(void) const {
        return this->importTable_rva;
      }


      triton::uint32 PeDataDirectory::getImportTable_size(void) const {
        return this->importTable_size;
      }


      triton::uint32 PeDataDirectory::getResourceTable_rva(void) const {
        return this->resourceTable_rva;
      }


      triton::uint32 PeDataDirectory::getResourceTable_size(void) const {
        return this->resourceTable_size;
      }


      triton::uint32 PeDataDirectory::getExceptionTable_rva(void) const {
        return this->exceptionTable_rva;
      }


      triton::uint32 PeDataDirectory::getExceptionTable_size(void) const {
        return this->exceptionTable_size;
      }


      triton::uint32 PeDataDirectory::getCertificateTable_rva(void) const {
        return this->certificateTable_rva;
      }


      triton::uint32 PeDataDirectory::getCertificateTable_size(void) const {
        return this->certificateTable_size;
      }


      triton::uint32 PeDataDirectory::getBaseRelocationTable_rva(void) const {
        return this->baseRelocationTable_rva;
      }


      triton::uint32 PeDataDirectory::getBaseRelocationTable_size(void) const {
        return this->baseRelocationTable_size;
      }


      triton::uint32 PeDataDirectory::getDebugTable_rva(void) const {
        return this->debugTable_rva;
      }


      triton::uint32 PeDataDirectory::getDebugTable_size(void) const {
        return this->debugTable_size;
      }


      triton::uint32 PeDataDirectory::getArchitectureTable_rva(void) const {
        return this->architectureTable_rva;
      }


      triton::uint32 PeDataDirectory::getArchitectureTable_size(void) const {
        return this->architectureTable_size;
      }


      triton::uint32 PeDataDirectory::getGlobalPtr_rva(void) const {
        return this->globalPtr_rva;
      }


      triton::uint32 PeDataDirectory::getGlobalPtr_size(void) const {
        return this->globalPtr_size;
      }


      triton::uint32 PeDataDirectory::getTlsTable_rva(void) const {
        return this->tlsTable_rva;
      }


      triton::uint32 PeDataDirectory::getTlsTable_size(void) const {
        return this->tlsTable_size;
      }


      triton::uint32 PeDataDirectory::getLoadConfigTable_rva(void) const {
        return this->loadConfigTable_rva;
      }


      triton::uint32 PeDataDirectory::getLoadConfigTable_size(void) const {
        return this->loadConfigTable_size;
      }


      triton::uint32 PeDataDirectory::getBoundImportTable_rva(void) const {
        return this->boundImportTable_rva;
      }


      triton::uint32 PeDataDirectory::getBoundImportTable_size(void) const {
        return this->boundImportTable_size;
      }


      triton::uint32 PeDataDirectory::getImportAddressTable_rva(void) const {
        return this->importAddressTable_rva;
      }


      triton::uint32 PeDataDirectory::getImportAddressTable_size(void) const {
        return this->importAddressTable_size;
      }


      triton::uint32 PeDataDirectory::getDelayImportDescriptor_rva(void) const {
        return this->delayImportDescriptor_rva;
      }


      triton::uint32 PeDataDirectory::getDelayImportDescriptor_size(void) const {
        return this->delayImportDescriptor_size;
      }


      triton::uint32 PeDataDirectory::getClrRuntimeHeader_rva(void) const {
        return this->clrRuntimeHeader_rva;
      }


      triton::uint32 PeDataDirectory::getClrRuntimeHeader_size(void) const {
        return this->clrRuntimeHeader_size;
      }


      triton::uint64 PeDataDirectory::getReserved(void) const {
        return this->reserved;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


