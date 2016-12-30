//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_PEBUILDER_H
#define TRITON_PEBUILDER_H

#include <iostream>
#include <vector>

#include "pe.hpp"

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

      /*! \class PeBuilder
       *  \brief A mutable PE container. */
      class PeBuilder : public Pe {
        protected:

          //! Content of each section
          std::vector<std::vector<triton::uint8> > sectionContent;

        public:
          //! Constructor.
          PeBuilder(const std::string& path);

          //! Destructor.
          virtual ~PeBuilder();

          //! Adds a new section to the binary.
          void addSection(const std::string name, triton::uint32 vsize, triton::uint32 rawsize, triton::uint32 characteristics);

          //! Saves the file conents.
          void save(const std::string &path);
      };

    /*! @} End of pe namespace */
    };
  /*! @} End of format namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_PEBUILDER_H */
