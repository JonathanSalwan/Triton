//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_BITSVECTOR_H
#define TRITON_BITSVECTOR_H

#include <utility>
#include "tritonTypes.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Architecture namespace
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

        //! Returns the vector's size
        triton::uint32 getVectorSize(void) const;

        //! Returns the pair<high, low>
        std::pair<triton::uint32, triton::uint32> getPair(void) const;

        //! Copy a BitsVector.
        void operator=(const BitsVector& other);

        //! Sets the highest bit's position
        void setHigh(triton::uint32 v);

        //! Sets the lower bit's position
        void setLow(triton::uint32 v);

        //! Sets the pair<high, low>'s position
        void setPair(std::pair<triton::uint32, triton::uint32> p);

        //! Constructor.
        BitsVector();

        //! Constructor.
        BitsVector(triton::uint32 high, triton::uint32 low);

        //! Constructor by copy.
        BitsVector(const triton::arch::BitsVector &copy);

        //! Destructor.
        ~BitsVector();
    };

    //! Displays a BitsVector.
    std::ostream &operator<<(std::ostream &stream, BitsVector bv);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_BITSVECTOR_H */

