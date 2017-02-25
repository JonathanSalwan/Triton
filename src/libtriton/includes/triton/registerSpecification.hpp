//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_REGISTERSPECIFICATION_H
#define TRITON_REGISTERSPECIFICATION_H

#include <string>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Triton namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    /*! \class RegisterSpecification
     *  \brief This class is used to describe the specification of a register.
     */
    class RegisterSpecification {
      protected:
        //! The name of the register.
        std::string name;

        //! The highest bit position.
        triton::uint32 high;

        //! The lower bit position.
        triton::uint32 low;

        //! The parent id of the register.
        triton::uint32 parentId;

      public:
        //! Constructor.
        RegisterSpecification();

        //! Constructor.
        RegisterSpecification(std::string& name, triton::uint32 high, triton::uint32 low, triton::uint32 parentId);

        //! Constructor by copy.
        RegisterSpecification(const RegisterSpecification& other);

        //! Destructor.
        virtual ~RegisterSpecification();

        //! Copies a RegisterSpecification.
        void operator=(const RegisterSpecification& other);

        //! Returns the name of the register.
        std::string getName(void) const;

        //! Returns the highest bit position of the register.
        triton::uint32 getHigh(void) const;

        //! Returns the lower bit position of the register.
        triton::uint32 getLow(void) const;

        //! Returns the parent id of the register.
        triton::uint32 getParentId(void) const;

        //! Sets the name of the registers.
        void setName(const std::string& name);

        //! Sets the highest bit position of the register.
        void setHigh(triton::uint32 high);

        //! Sets the lower bit position of the register.
        void setLow(triton::uint32 low);

        //! Sets the parent id of the register.
        void setParentId(triton::uint32 parentId);
    };

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_REGISTERSPECIFICATION_H */
