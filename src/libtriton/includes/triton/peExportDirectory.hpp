//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEEXPORTDIRECTORY_H
#define TRITON_PEEXPORTDIRECTORY_H

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


      //! The PE export entry structure.
      struct PeExportEntry {
        /*!
         * \description Indicates whether the entry is a forward (reference by name to another function perhaps in another DLL).
         */
        bool isForward;

        /*!
         * \description If the export is not a forward reference, this is the address of the exported function.
         */
        triton::uint32 exportRVA;

        /*!
         * \description If the export is a forward reference, this is the address of the name of the target function.
         */
        triton::uint32 forwarderRVA;

        /*!
         * \description If the export is a forward reference, this is the name of the target function.
         */
        std::string forwarderName;

        /*!
         * \description The address of the name of the exported function.
         */
        triton::uint32 exportNameRVA;

        /*!
         * \description The name of the exported function.
         */
        std::string exportName;

        /*!
         * \description The ordinal number of the target function.
         */
        triton::uint16 ordinal;
      };


      /*! \class PeExportDirectory
       *  \brief PE Export Directory Table */
      class PeExportDirectory {
        protected:
          //! The PE export directory structure
          struct {
            /*!
             * \description Reserved, must be 0.
             */
            triton::uint32 exportFlags;

            /*!
             * \description The time and date that the export data was created.
             */
            triton::uint32 timeDateStamp;

            /*!
             * \description The major version number. The major and minor version numbers can be set by the user.
             */
            triton::uint16 majorVersion;

            /*!
             * \description The minor version number.
             */
            triton::uint16 minorVersion;

            /*!
             * \description The address of the ASCII string that contains the name of the DLL. This address is relative to the image base.
             */
            triton::uint32 nameRVA;

            /*!
             * \description The starting ordinal number for exports in this image. This field specifies the starting ordinal number for the export address table. It is usually set to 1.
             */
            triton::uint32 ordinalBase;

            /*!
             * \description The number of entries in the export address table.
             */
            triton::uint32 addressTableEntries;

            /*!
             * \description The number of entries in the name pointer table. This is also the number of entries in the ordinal table.
             */
            triton::uint32 numberOfNamePointers;

            /*!
             * \description The address of the export address table, relative to the image base.
             */
            triton::uint32 exportAddressTableRVA;

            /*!
             * \description The address of the export name pointer table, relative to the image base. The table size is given by the Number of Name Pointers field.
             */
            triton::uint32 namePointerRVA;

            /*!
             * \description The address of the ordinal table, relative to the image base.
             */
            triton::uint32 ordinalTableRVA;
          } st;

          /*!
           * \description Name, based on nameRVA.
           */
          std::string name;

          /*!
           * \description The export table entries.
           */
          std::vector<PeExportEntry> entries;

        public:

          //! Constructor.
          PeExportDirectory();

          //! Copy constructor.
          PeExportDirectory(const PeExportDirectory& copy);

          //! Copy assignment operator.
          PeExportDirectory& operator=(const PeExportDirectory& copy);

          //! Destructor.
          ~PeExportDirectory();

          //! Parses the export directory.
          void parse(const triton::uint8* raw);

          //! Returns the exportFlags.
          triton::uint32 getExportFlags(void) const;

          //! Returns the timeDateStamp.
          triton::uint32 getTimeDateStamp(void) const;

          //! Returns the majorVersion.
          triton::uint16 getMajorVersion(void) const;

          //! Returns the minorVersion.
          triton::uint16 getMinorVersion(void) const;

          //! Returns the nameRVA.
          triton::uint32 getNameRVA(void) const;

          //! Returns the ordinalBase.
          triton::uint32 getOrdinalBase(void) const;

          //! Returns the addressTableEntries.
          triton::uint32 getAddressTableEntries(void) const;

          //! Returns the numberOfNamePointers.
          triton::uint32 getNumberOfNamePointers(void) const;

          //! Returns the exportAddressTableRVA.
          triton::uint32 getExportAddressTableRVA(void) const;

          //! Returns the namePointerRVA.
          triton::uint32 getNamePointerRVA(void) const;

          //! Returns the ordinalTableRVA.
          triton::uint32 getOrdinalTableRVA(void) const;

          //! Sets the name.
          void setName(const std::string& name);

          //! Returns the name.
          const std::string& getName(void) const;

          //! Adds an entry.
          void addEntry(const PeExportEntry& entry);

          //! Returns the entries.
          const std::vector<PeExportEntry>& getEntries(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEEXPORTDIRECTORY_H */
