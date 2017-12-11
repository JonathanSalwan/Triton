//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICVARIABLE_H
#define TRITON_SYMBOLICVARIABLE_H

#include <string>

#include <triton/dllexport.hpp>
#include <triton/symbolicEnums.hpp>
#include <triton/tritonTypes.hpp>



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
      class SymbolicVariable {
        protected:
          //! The symbolic variable kind. \sa triton::engines::symbolic::symkind_e
          symkind_e kind;

          //! The comment of the symbolic variable.
          std::string comment;

          //! The name of the symbolic variable. Names are always something like this: SymVar_X. \sa TRITON_SYMVAR_NAME
          std::string name;

          //! The id of the symbolic variable. This id is unique.
          triton::usize id;

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
          TRITON_EXPORT SymbolicVariable(symkind_e kind,
                                         triton::uint64 kindValue,
                                         triton::usize id,
                                         triton::uint32 size,
                                         const std::string& comment);

          //! Constructor by copy.
          TRITON_EXPORT SymbolicVariable(const SymbolicVariable& other);

          //! Operator.
          TRITON_EXPORT SymbolicVariable& operator=(const SymbolicVariable& other);

          //! Returns the symbolic variable kind. \sa triton::engines::symbolic::symkind_e.
          TRITON_EXPORT symkind_e getKind(void) const;

          //! Returns the comment of the symbolic variable.
          TRITON_EXPORT const std::string& getComment(void) const;

          //! Returns the name of the symbolic variable.
          TRITON_EXPORT const std::string& getName(void) const;

          //! Returns the id of the symbolic variable. This id is unique.
          TRITON_EXPORT triton::usize getId(void) const;

          //! Returns the kind value of the symbolic variable.
          TRITON_EXPORT triton::uint64 getKindValue(void) const;

          //! Returns the size (in bits) of the symbolic variable.
          TRITON_EXPORT triton::uint32 getSize(void) const;

          //! Sets the comment of the symbolic variable.
          TRITON_EXPORT void setComment(const std::string& comment);
      };

      //! Displays a symbolic variable.
      TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const SymbolicVariable& symVar);

      //! Displays a symbolic variable.
      TRITON_EXPORT std::ostream& operator<<(std::ostream& stream, const SymbolicVariable* symVar);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICVARIABLE_H */

