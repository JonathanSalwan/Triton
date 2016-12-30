//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEIMPORTDIRECTORY_H
#define TRITON_PEIMPORTDIRECTORY_H

#include "peEnums.hpp"
#include "tritonTypes.hpp"

#include <vector>

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

      //! The PE import directory structure.

      /*! \class PEImportLookup
       *  \brief PE Import Lookup Table entry */
      struct PeImportLookup {
          bool importByName;
          triton::uint16 ordinalNumber; //contains "hint" if importByName
          std::string name; //only if importByName
      };

      /*! \class PeImportDirectory
       *  \brief PE Import Directory Table entry */
      class PeImportDirectory {
      protected:

          //this struct contains the items found directly in the binary data
          struct {
            /*!
             * \description The RVA of the import lookup table. This table contains a name or ordinal for each import. (The name “Characteristics” is used in Winnt.h, but no longer describes this field.)
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
          triton::uint32 getImportLookupTableRVA() const;

          //! Returns the timeDateStamp.
          triton::uint32 getTimeDateStamp() const;

          //! Returns the forwarderChain.
          triton::uint32 getForwarderChain() const;

          //! Returns the nameRVA.
          triton::uint32 getNameRVA() const;

          //! Returns the importAddressTableRVA.
          triton::uint32 getImportAddressTableRVA() const;

          //! Sets the name.
          void setName(std::string name);

          //! Returns the name.
          std::string getName() const;

          //! Adds an entry.
          void addEntry(const PeImportLookup &entry);

          //! Returns the entries.
          const std::vector<PeImportLookup> &getEntries() const;
          
      };


    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEIMPORTDIRECTORY_H */
