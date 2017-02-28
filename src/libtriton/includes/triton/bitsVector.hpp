//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_BITSVECTOR_H
#define TRITON_BITSVECTOR_H

#include <utility>
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
        //! Returns the highest bit
        triton::uint32 getHigh(void) const;

        //! Returns the lower bit
        triton::uint32 getLow(void) const;

        //! Returns the size of the vector
        triton::uint32 getVectorSize(void) const;

        //! Returns the max possible value of the bitvector.
        triton::uint512 getMaxValue(void) const;

        //! Copy a BitsVector.
        void operator=(const BitsVector& other);

        //! Sets the highest bit position
        void setHigh(triton::uint32 v);

        //! Sets the lower bit position
        void setLow(triton::uint32 v);

        //! Sets the pair<high, low> position
        void setPair(std::pair<triton::uint32, triton::uint32> p);

        //! Constructor.
        BitsVector();

        //! Constructor.
        BitsVector(triton::uint32 high, triton::uint32 low);

        //! Constructor by copy.
        BitsVector(const triton::arch::BitsVector& copy);

        //! Destructor.
        virtual ~BitsVector();
    };

    //! Displays a BitsVector.
    std::ostream& operator<<(std::ostream& stream, const BitsVector& bv);

    //! Displays a BitsVector.
    std::ostream& operator<<(std::ostream& stream, const BitsVector* bv);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BITSVECTOR_H */

