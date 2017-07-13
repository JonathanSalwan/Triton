//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_REGISTEROPERAND_H
#define TRITON_REGISTEROPERAND_H

#include <string>
#include <ostream>

#include <triton/bitsVector.hpp>
#include <triton/cpuSize.hpp>
#include <triton/operandInterface.hpp>
#include <triton/registers_e.hpp>
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

    //! Used for a Register constructor.
    class CpuInterface;

    /*! \class Register
     *  \brief This class is used when an instruction has a register operand.
     */
    class Register : public BitsVector, public OperandInterface {
      protected:
        //! The name of the register.
        std::string name;

        //! The id of the register.
        triton::arch::registers_e id;

        //! The parent id of the register.
        triton::arch::registers_e parent;

        //! Copy a Register.
        void copy(const Register& other);

      public:
        //! Constructor.
        Register();

        //! Constructor.
        Register(triton::arch::registers_e regId, std::string name, triton::arch::registers_e parent, triton::uint32 high, triton::uint32 low);

        //! Constructor.
        Register(const triton::arch::CpuInterface&, triton::arch::registers_e regId);

        //! Constructor.
        Register(const Register& other);

        //! Returns the parent id of the register.
        registers_e getParent(void) const;

        //! Returns true if `other` and `self` overlap.
        bool isOverlapWith(const Register& other) const;

        //! Returns the name of the register.
        std::string getName(void) const;

        //! Returns the highest bit of the register vector. \sa BitsVector::getHigh()
        triton::uint32 getAbstractHigh(void) const;

        //! Returns the lower bit of the register vector. \sa BitsVector::getLow()
        triton::uint32 getAbstractLow(void) const;

        //! Returns the size (in bits) of the register.
        triton::uint32 getBitSize(void) const;

        //! Returns the id of the register.
        triton::arch::registers_e getId(void) const;

        //! Returns the size (in bytes) of the register.
        triton::uint32 getSize(void) const;

        //! Returns the type of the operand (triton::arch::OP_REG).
        triton::uint32 getType(void) const;

        //! Compare two registers specifications
        bool operator==(const Register& other) const;

        //! Compare two registers specifications
        bool operator!=(const Register& other) const;

        //! Copies a Register.
        void operator=(const Register& other);
    };

    //! Displays a Register.
    std::ostream& operator<<(std::ostream& stream, const Register& reg);

    //! Displays a Register.
    std::ostream& operator<<(std::ostream& stream, const Register* reg);

    //! Compares two Register
    bool operator<(const Register& reg1, const Register& reg2);

  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_REGISTEROPERAND_H */
