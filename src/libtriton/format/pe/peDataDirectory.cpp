//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdio>

#include <triton/exceptions.hpp>
#include <triton/peDataDirectory.hpp>



namespace triton {
  namespace format {
    namespace pe {

      PeDataDirectory::PeDataDirectory() {
        this->st.exportTable_rva            = 0;
        this->st.exportTable_size           = 0;
        this->st.importTable_rva            = 0;
        this->st.importTable_size           = 0;
        this->st.resourceTable_rva          = 0;
        this->st.resourceTable_size         = 0;
        this->st.exceptionTable_rva         = 0;
        this->st.exceptionTable_size        = 0;
        this->st.certificateTable_rva       = 0;
        this->st.certificateTable_size      = 0;
        this->st.baseRelocationTable_rva    = 0;
        this->st.baseRelocationTable_size   = 0;
        this->st.debugTable_rva             = 0;
        this->st.debugTable_size            = 0;
        this->st.architectureTable_rva      = 0;
        this->st.architectureTable_size     = 0;
        this->st.globalPtr_rva              = 0;
        this->st.globalPtr_size             = 0;
        this->st.tlsTable_rva               = 0;
        this->st.tlsTable_size              = 0;
        this->st.loadConfigTable_rva        = 0;
        this->st.loadConfigTable_size       = 0;
        this->st.boundImportTable_rva       = 0;
        this->st.boundImportTable_size      = 0;
        this->st.importAddressTable_rva     = 0;
        this->st.importAddressTable_size    = 0;
        this->st.delayImportDescriptor_rva  = 0;
        this->st.delayImportDescriptor_size = 0;
        this->st.clrRuntimeHeader_rva       = 0;
        this->st.clrRuntimeHeader_size      = 0;
        this->st.reserved                   = 0;
      }


      PeDataDirectory::PeDataDirectory(const PeDataDirectory& copy) {
        this->st.exportTable_rva            = copy.st.exportTable_rva;
        this->st.exportTable_size           = copy.st.exportTable_size;
        this->st.importTable_rva            = copy.st.importTable_rva;
        this->st.importTable_size           = copy.st.importTable_size;
        this->st.resourceTable_rva          = copy.st.resourceTable_rva;
        this->st.resourceTable_size         = copy.st.resourceTable_size;
        this->st.exceptionTable_rva         = copy.st.exceptionTable_rva;
        this->st.exceptionTable_size        = copy.st.exceptionTable_size;
        this->st.certificateTable_rva       = copy.st.certificateTable_rva;
        this->st.certificateTable_size      = copy.st.certificateTable_size;
        this->st.baseRelocationTable_rva    = copy.st.baseRelocationTable_rva;
        this->st.baseRelocationTable_size   = copy.st.baseRelocationTable_size;
        this->st.debugTable_rva             = copy.st.debugTable_rva;
        this->st.debugTable_size            = copy.st.debugTable_size;
        this->st.architectureTable_rva      = copy.st.architectureTable_rva;
        this->st.architectureTable_size     = copy.st.architectureTable_size;
        this->st.globalPtr_rva              = copy.st.globalPtr_rva;
        this->st.globalPtr_size             = copy.st.globalPtr_size;
        this->st.tlsTable_rva               = copy.st.tlsTable_rva;
        this->st.tlsTable_size              = copy.st.tlsTable_size;
        this->st.loadConfigTable_rva        = copy.st.loadConfigTable_rva;
        this->st.loadConfigTable_size       = copy.st.loadConfigTable_size;
        this->st.boundImportTable_rva       = copy.st.boundImportTable_rva;
        this->st.boundImportTable_size      = copy.st.boundImportTable_size;
        this->st.importAddressTable_rva     = copy.st.importAddressTable_rva;
        this->st.importAddressTable_size    = copy.st.importAddressTable_size;
        this->st.delayImportDescriptor_rva  = copy.st.delayImportDescriptor_rva;
        this->st.delayImportDescriptor_size = copy.st.delayImportDescriptor_size;
        this->st.clrRuntimeHeader_rva       = copy.st.clrRuntimeHeader_rva;
        this->st.clrRuntimeHeader_size      = copy.st.clrRuntimeHeader_size;
        this->st.reserved                   = copy.st.reserved;
      }


      PeDataDirectory::~PeDataDirectory() {
      }


      PeDataDirectory& PeDataDirectory::operator=(const PeDataDirectory& copy) {
        if (this == &copy)
            return *this;

        this->st.exportTable_rva            = copy.st.exportTable_rva;
        this->st.exportTable_size           = copy.st.exportTable_size;
        this->st.importTable_rva            = copy.st.importTable_rva;
        this->st.importTable_size           = copy.st.importTable_size;
        this->st.resourceTable_rva          = copy.st.resourceTable_rva;
        this->st.resourceTable_size         = copy.st.resourceTable_size;
        this->st.exceptionTable_rva         = copy.st.exceptionTable_rva;
        this->st.exceptionTable_size        = copy.st.exceptionTable_size;
        this->st.certificateTable_rva       = copy.st.certificateTable_rva;
        this->st.certificateTable_size      = copy.st.certificateTable_size;
        this->st.baseRelocationTable_rva    = copy.st.baseRelocationTable_rva;
        this->st.baseRelocationTable_size   = copy.st.baseRelocationTable_size;
        this->st.debugTable_rva             = copy.st.debugTable_rva;
        this->st.debugTable_size            = copy.st.debugTable_size;
        this->st.architectureTable_rva      = copy.st.architectureTable_rva;
        this->st.architectureTable_size     = copy.st.architectureTable_size;
        this->st.globalPtr_rva              = copy.st.globalPtr_rva;
        this->st.globalPtr_size             = copy.st.globalPtr_size;
        this->st.tlsTable_rva               = copy.st.tlsTable_rva;
        this->st.tlsTable_size              = copy.st.tlsTable_size;
        this->st.loadConfigTable_rva        = copy.st.loadConfigTable_rva;
        this->st.loadConfigTable_size       = copy.st.loadConfigTable_size;
        this->st.boundImportTable_rva       = copy.st.boundImportTable_rva;
        this->st.boundImportTable_size      = copy.st.boundImportTable_size;
        this->st.importAddressTable_rva     = copy.st.importAddressTable_rva;
        this->st.importAddressTable_size    = copy.st.importAddressTable_size;
        this->st.delayImportDescriptor_rva  = copy.st.delayImportDescriptor_rva;
        this->st.delayImportDescriptor_size = copy.st.delayImportDescriptor_size;
        this->st.clrRuntimeHeader_rva       = copy.st.clrRuntimeHeader_rva;
        this->st.clrRuntimeHeader_size      = copy.st.clrRuntimeHeader_size;
        this->st.reserved                   = copy.st.reserved;

        return *this;
      }


      triton::uint32 PeDataDirectory::getSize(void) const {
        return sizeof(this->st);
      }


      void PeDataDirectory::parse(const triton::uint8* raw) {
        std::memcpy(&this->st, raw, sizeof(this->st));
      }


      void PeDataDirectory::save(std::ostream& os) const {
        os.write(reinterpret_cast<const char*>(&this->st), sizeof(this->st));
      }


      triton::uint32 PeDataDirectory::getExportTable_rva(void) const {
        return this->st.exportTable_rva;
      }


      triton::uint32 PeDataDirectory::getExportTable_size(void) const {
        return this->st.exportTable_size;
      }


      triton::uint32 PeDataDirectory::getImportTable_rva(void) const {
        return this->st.importTable_rva;
      }


      triton::uint32 PeDataDirectory::getImportTable_size(void) const {
        return this->st.importTable_size;
      }


      triton::uint32 PeDataDirectory::getResourceTable_rva(void) const {
        return this->st.resourceTable_rva;
      }


      triton::uint32 PeDataDirectory::getResourceTable_size(void) const {
        return this->st.resourceTable_size;
      }


      triton::uint32 PeDataDirectory::getExceptionTable_rva(void) const {
        return this->st.exceptionTable_rva;
      }


      triton::uint32 PeDataDirectory::getExceptionTable_size(void) const {
        return this->st.exceptionTable_size;
      }


      triton::uint32 PeDataDirectory::getCertificateTable_rva(void) const {
        return this->st.certificateTable_rva;
      }


      triton::uint32 PeDataDirectory::getCertificateTable_size(void) const {
        return this->st.certificateTable_size;
      }


      triton::uint32 PeDataDirectory::getBaseRelocationTable_rva(void) const {
        return this->st.baseRelocationTable_rva;
      }


      triton::uint32 PeDataDirectory::getBaseRelocationTable_size(void) const {
        return this->st.baseRelocationTable_size;
      }


      triton::uint32 PeDataDirectory::getDebugTable_rva(void) const {
        return this->st.debugTable_rva;
      }


      triton::uint32 PeDataDirectory::getDebugTable_size(void) const {
        return this->st.debugTable_size;
      }


      triton::uint32 PeDataDirectory::getArchitectureTable_rva(void) const {
        return this->st.architectureTable_rva;
      }


      triton::uint32 PeDataDirectory::getArchitectureTable_size(void) const {
        return this->st.architectureTable_size;
      }


      triton::uint32 PeDataDirectory::getGlobalPtr_rva(void) const {
        return this->st.globalPtr_rva;
      }


      triton::uint32 PeDataDirectory::getGlobalPtr_size(void) const {
        return this->st.globalPtr_size;
      }


      triton::uint32 PeDataDirectory::getTlsTable_rva(void) const {
        return this->st.tlsTable_rva;
      }


      triton::uint32 PeDataDirectory::getTlsTable_size(void) const {
        return this->st.tlsTable_size;
      }


      triton::uint32 PeDataDirectory::getLoadConfigTable_rva(void) const {
        return this->st.loadConfigTable_rva;
      }


      triton::uint32 PeDataDirectory::getLoadConfigTable_size(void) const {
        return this->st.loadConfigTable_size;
      }


      triton::uint32 PeDataDirectory::getBoundImportTable_rva(void) const {
        return this->st.boundImportTable_rva;
      }


      triton::uint32 PeDataDirectory::getBoundImportTable_size(void) const {
        return this->st.boundImportTable_size;
      }


      triton::uint32 PeDataDirectory::getImportAddressTable_rva(void) const {
        return this->st.importAddressTable_rva;
      }


      triton::uint32 PeDataDirectory::getImportAddressTable_size(void) const {
        return this->st.importAddressTable_size;
      }


      triton::uint32 PeDataDirectory::getDelayImportDescriptor_rva(void) const {
        return this->st.delayImportDescriptor_rva;
      }


      triton::uint32 PeDataDirectory::getDelayImportDescriptor_size(void) const {
        return this->st.delayImportDescriptor_size;
      }


      triton::uint32 PeDataDirectory::getClrRuntimeHeader_rva(void) const {
        return this->st.clrRuntimeHeader_rva;
      }


      triton::uint32 PeDataDirectory::getClrRuntimeHeader_size(void) const {
        return this->st.clrRuntimeHeader_size;
      }


      triton::uint64 PeDataDirectory::getReserved(void) const {
        return this->st.reserved;
      }

    }; /* pe namespace */
  }; /* format namespace */
}; /* triton namespace */


