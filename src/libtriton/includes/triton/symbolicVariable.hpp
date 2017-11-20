//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICVARIABLE_H
#define TRITON_SYMBOLICVARIABLE_H

#include <triton/astContext.hpp>          // for Context
#include <triton/symbolicEnums.hpp>
#include <triton/symbolicValue.hpp>
#include <tritoncore/types.hpp>

#include <string>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! The Symbolic Execution namespace
    namespace symbolic {
    /*!
     *  \ingroup engines
     *  \addtogroup symbolic
     *  @{
     */

      /*! \class SymbolicVariable
          \brief The symbolic variable class. */
      class SymbolicVariable: public SymbolicValue {

        protected:
          //! The name of the symbolic variable. Names are always something like this: SymVar_X. \sa TRITON_SYMVAR_NAME
          std::string name;

          /*! \brief The kind value of the symbolic variable.
           *
           * \details If the symbolic varialbe is a triton::engines::symbolic::REG, this value contains the register ID.
           * Otherwise, if the symbolic varialbe is a triton::engines::symbolic::MEM, this value contains the address of the
           * memory access.
           */
          triton::uint64 kindValue;

          //! The size (in bits) of the symbolic variable.
          triton::uint32 size;

        public:
          //! Constructor.
          SymbolicVariable(triton::AstContext& astCtxt,
                           symkind_e kind,
                           triton::uint64 kindValue,
                           triton::usize id,
                           triton::uint32 size,
                           const std::string& comment);

          //! Constructor by copy.
          SymbolicVariable(const SymbolicVariable& copy);

          //! Returns the name of the symbolic variable.
          const std::string& getName(void) const;

          //! Returns the kind value of the symbolic variable.
          triton::uint64 getKindValue(void) const;

          //! Returns the size (in bits) of the symbolic variable.
          triton::uint32 getSize(void) const;
      };

      //! Displays a symbolic variable.
      std::ostream& operator<<(std::ostream& stream, const SymbolicVariable& symVar);

      //! Displays a symbolic variable.
      std::ostream& operator<<(std::ostream& stream, const SymbolicVariable* symVar);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICVARIABLE_H */

