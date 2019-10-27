//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_BITSVECTOR_H
#define TRITON_BITSVECTOR_H

#include <utility>

#include <triton/triton_export.h>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class BitsVector
     *  \brief This class is used to deal with registers and memory as bits vector.
     */
    class BitsVector {
      protected:
        //! The highest bit of the bitvector
        triton::uint32 high;

        //! The lower bit of the bitvector
        triton::uint32 low;

      public:
        //! Constructor.
        TRITON_EXPORT BitsVector();

        //! Constructor.
        TRITON_EXPORT BitsVector(triton::uint32 high, triton::uint32 low);

        //! Constructor by copy.
        TRITON_EXPORT BitsVector(const triton::arch::BitsVector& other);

        //! Copy a BitsVector.
        TRITON_EXPORT BitsVector& operator=(const BitsVector& other);

        //! Returns the highest bit
        TRITON_EXPORT triton::uint32 getHigh(void) const;

        //! Returns the lower bit
        TRITON_EXPORT triton::uint32 getLow(void) const;

        //! Returns the size in bits of the vector
        TRITON_EXPORT triton::uint32 getVectorSize(void) const;

        //! Returns the max possible value of the bitvector.
        TRITON_EXPORT triton::uint512 getMaxValue(void) const;

        //! Sets the highest bit position
        TRITON_EXPORT void setHigh(triton::uint32 v);

        //! Sets the lower bit position
        TRITON_EXPORT void setLow(triton::uint32 v);

        //! Sets the pair<high, low> position
        TRITON_EXPORT void setPair(std::pair<triton::uint32, triton::uint32> p);
    };

    //! Displays a BitsVector.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const BitsVector& bv);

    //! Displays a BitsVector.
    TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const BitsVector* bv);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BITSVECTOR_H */
