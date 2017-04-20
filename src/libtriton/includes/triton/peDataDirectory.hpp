//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEDATADIRECTORY_H
#define TRITON_PEDATADIRECTORY_H

#include <vector>

#include <triton/peEnums.hpp>
#include <triton/tritonTypes.hpp>



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

      /*! \class PeDataDirectory
       *  \brief PE data directory */
      class PeDataDirectory {
        protected:
          //! The data directory structure fields.
          struct {
            /*!
             * \details The export table address.
             */
            triton::uint32 exportTable_rva;

            /*!
             * \details The export table size.
             */
            triton::uint32 exportTable_size;

            /*!
             * \details The import table address
             */
            triton::uint32 importTable_rva;

            /*!
             * \details The import table size.
             */
            triton::uint32 importTable_size;

            /*!
             * \details The resource table address.
             */
            triton::uint32 resourceTable_rva;

            /*!
             * \details The resource table size.
             */
            triton::uint32 resourceTable_size;

            /*!
             * \details The exception table address.
             */
            triton::uint32 exceptionTable_rva;

            /*!
             * \details The exception table size.
             */
            triton::uint32 exceptionTable_size;

            /*!
             * \details The attribute certificate table address.
             */
            triton::uint32 certificateTable_rva;

            /*!
             * \details The attribute certificate table size.
             */
            triton::uint32 certificateTable_size;

            /*!
             * \details The base relocation table address.
             */
            triton::uint32 baseRelocationTable_rva;

            /*!
             * \details The base relocation table size.
             */
            triton::uint32 baseRelocationTable_size;

            /*!
             * \details The debug data starting address.
             */
            triton::uint32 debugTable_rva;

            /*!
             * \details The debug data size.
             */
            triton::uint32 debugTable_size;

            /*!
             * \details Reserved, must be 0
             */
            triton::uint32 architectureTable_rva;

            /*!
             * \details Reserved, must be 0
             */
            triton::uint32 architectureTable_size;

            /*!
             * \details The RVA of the value to be stored in the global pointer register.
             */
            triton::uint32 globalPtr_rva;

            /*!
             * \details Must be set to zero.
             */
            triton::uint32 globalPtr_size;

            /*!
             * \details The thread local storage (TLS) table address.
             */
            triton::uint32 tlsTable_rva;

            /*!
             * \details The thread local storage (TLS) table size.
             */
            triton::uint32 tlsTable_size;

            /*!
             * \details The load configuration table address.
             */
            triton::uint32 loadConfigTable_rva;

            /*!
             * \details The load configuration table size.
             */
            triton::uint32 loadConfigTable_size;

            /*!
             * \details The bound import table address.
             */
            triton::uint32 boundImportTable_rva;

            /*!
             * \details The bound import table size.
             */
            triton::uint32 boundImportTable_size;

            /*!
             * \details The import address table address.
             */
            triton::uint32 importAddressTable_rva;

            /*!
             * \details The import address table size.
             */
            triton::uint32 importAddressTable_size;

            /*!
             * \details The delay import descriptor address.
             */
            triton::uint32 delayImportDescriptor_rva;

            /*!
             * \details The delay import descriptor size.
             */
            triton::uint32 delayImportDescriptor_size;

            /*!
             * \details The CLR runtime header address.
             */
            triton::uint32 clrRuntimeHeader_rva;

            /*!
             * \details The CLR runtime header size.
             */
            triton::uint32 clrRuntimeHeader_size;

            /*!
             * \details Reserved, must be zero
             */
            triton::uint64 reserved;
          } st;

        public:
          //! Constructor.
          PeDataDirectory();

          //! Copy constructor.
          PeDataDirectory(const PeDataDirectory& copy);

          //! Copy assignment operator.
          PeDataDirectory& operator=(const PeDataDirectory& copy);

          //! Destructor.
          ~PeDataDirectory();

          //! Returns the size of the structure.
          triton::uint32 getSize(void) const;

          //! Parses the header.
          void parse(const triton::uint8* raw);

          //! Saves the header to file.
          void save(std::ostream& os) const;

          //! Returns the exportTable_rva.
          triton::uint32 getExportTable_rva(void) const;

          //! Returns the exportTable_size.
          triton::uint32 getExportTable_size(void) const;

          //! Returns the importTable_rva.
          triton::uint32 getImportTable_rva(void) const;

          //! Returns the importTable_size.
          triton::uint32 getImportTable_size(void) const;

          //! Returns the resourceTable_rva.
          triton::uint32 getResourceTable_rva(void) const;

          //! Returns the resourceTable_size.
          triton::uint32 getResourceTable_size(void) const;

          //! Returns the exceptionTable_rva.
          triton::uint32 getExceptionTable_rva(void) const;

          //! Returns the exceptionTable_size.
          triton::uint32 getExceptionTable_size(void) const;

          //! Returns the certificateTable_rva.
          triton::uint32 getCertificateTable_rva(void) const;

          //! Returns the certificateTable_size.
          triton::uint32 getCertificateTable_size(void) const;

          //! Returns the baseRelocationTable_rva.
          triton::uint32 getBaseRelocationTable_rva(void) const;

          //! Returns the baseRelocationTable_size.
          triton::uint32 getBaseRelocationTable_size(void) const;

          //! Returns the debugTable_rva.
          triton::uint32 getDebugTable_rva(void) const;

          //! Returns the debugTable_size.
          triton::uint32 getDebugTable_size(void) const;

          //! Returns the architectureTable_rva.
          triton::uint32 getArchitectureTable_rva(void) const;

          //! Returns the architectureTable_size.
          triton::uint32 getArchitectureTable_size(void) const;

          //! Returns the globalPtr_rva.
          triton::uint32 getGlobalPtr_rva(void) const;

          //! Returns the globalPtr_size.
          triton::uint32 getGlobalPtr_size(void) const;

          //! Returns the tlsTable_rva.
          triton::uint32 getTlsTable_rva(void) const;

          //! Returns the tlsTable_size.
          triton::uint32 getTlsTable_size(void) const;

          //! Returns the loadConfigTable_rva.
          triton::uint32 getLoadConfigTable_rva(void) const;

          //! Returns the loadConfigTable_size.
          triton::uint32 getLoadConfigTable_size(void) const;

          //! Returns the boundImportTable_rva.
          triton::uint32 getBoundImportTable_rva(void) const;

          //! Returns the boundImportTable_size.
          triton::uint32 getBoundImportTable_size(void) const;

          //! Returns the importAddressTable_rva.
          triton::uint32 getImportAddressTable_rva(void) const;

          //! Returns the importAddressTable_size.
          triton::uint32 getImportAddressTable_size(void) const;

          //! Returns the delayImportDescriptor_rva.
          triton::uint32 getDelayImportDescriptor_rva(void) const;

          //! Returns the delayImportDescriptor_size.
          triton::uint32 getDelayImportDescriptor_size(void) const;

          //! Returns the clrRuntimeHeader_rva.
          triton::uint32 getClrRuntimeHeader_rva(void) const;

          //! Returns the clrRuntimeHeader_size.
          triton::uint32 getClrRuntimeHeader_size(void) const;

          //! Returns the reserved.
          triton::uint64 getReserved(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEDATADIRECTORY_H */
