//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEIMPORTDIRECTORY_H
#define TRITON_PEIMPORTDIRECTORY_H

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

      //! The PE Import Lookup Table entry.
      struct PeImportLookup {
        /*!
         * \description Indicates whether the import is by name or ordinal number.
         */
        bool importByName;

        /*!
         * \description If the import is by ordinal number, this is the ordinal numer, otherwise it's the "hint" that accompanies the import by name.
         */
        triton::uint16 ordinalNumber;

        /*!
         * \description If the import is by name, this is the name of the imported function.
         */
        std::string name;
      };


      /*! \class PeImportDirectory
       *  \brief PE Import Directory Table entry */
      class PeImportDirectory {
        protected:

          //! The PE import directory structure
          struct {
            /*!
             * \description The RVA of the import lookup table. This table contains a name or ordinal for each import. (The name "Characteristics" is used in Winnt.h, but no longer describes this field.)
             */
            triton::uint32 importLookupTableRVA;

            /*!
             * \description The stamp that is set to zero until the image is bound. After the image is bound, this field is set to the time/data stamp of the DLL.
             */
            triton::uint32 timeDateStamp;

            /*!
             * \description The index of the first forwarder reference.
             */
            triton::uint32 forwarderChain;

            /*!
             * \description The address of an ASCII string that contains the name of the DLL. This address is relative to the image base.
             */
            triton::uint32 nameRVA;

            /*!
             * \description The RVA of the import address table. The contents of this table are identical to the contents of the import lookup table until the image is bound.
             */
            triton::uint32 importAddressTableRVA;
          } st;

          /*!
           * \description The name at nameRVA as a string.
           */
          std::string name;

          /*!
           * \description The list of entries in the import directory.
           */
          std::vector<PeImportLookup> entries;

        public:

          //! Constructor.
          PeImportDirectory();

          //! Copy constructor.
          PeImportDirectory(const PeImportDirectory &copy);

          //! Copy assignment operator.
          PeImportDirectory &operator=(const PeImportDirectory &copy);

          //! Destructor.
          ~PeImportDirectory();

          //! Parses the import directory. Returns whether it was successful.
          bool parse(const triton::uint8* raw);

          //! Returns the importLookupTableRVA.
          triton::uint32 getImportLookupTableRVA(void) const;

          //! Returns the timeDateStamp.
          triton::uint32 getTimeDateStamp(void) const;

          //! Returns the forwarderChain.
          triton::uint32 getForwarderChain(void) const;

          //! Returns the nameRVA.
          triton::uint32 getNameRVA(void) const;

          //! Returns the importAddressTableRVA.
          triton::uint32 getImportAddressTableRVA(void) const;

          //! Sets the name.
          void setName(const std::string& name);

          //! Returns the name.
          const std::string& getName(void) const;

          //! Adds an entry.
          void addEntry(const PeImportLookup& entry);

          //! Returns the entries.
          const std::vector<PeImportLookup>& getEntries(void) const;
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEIMPORTDIRECTORY_H */
