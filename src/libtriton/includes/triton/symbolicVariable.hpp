//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICVARIABLE_H
#define TRITON_SYMBOLICVARIABLE_H

#include <string>

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
           * \description If the symbolic varialbe is a triton::engines::symbolic::REG, this value contains the register ID.
           * Otherwise, if the symbolic varialbe is a triton::engines::symbolic::MEM, this value contains the address of the
           * memory access.
           */
          triton::uint64 kindValue;

          //! The size (in bits) of the symbolic variable.
          triton::uint32 size;

          //! The concrete value of the symbolic variable.
          triton::uint512 concreteValue;

        public:
          //! Constructor.
          SymbolicVariable(symkind_e kind,
                           triton::uint64 kindValue,
                           triton::usize id,
                           triton::uint32 size,
                           const std::string& comment,
                           triton::uint512 concreteValue=0);

          //! Constructor by copy.
          SymbolicVariable(const SymbolicVariable& copy);

          //! Destructor.
          virtual ~SymbolicVariable();

          //! Returns the symbolic variable kind. \sa triton::engines::symbolic::symkind_e.
          symkind_e getKind(void) const;

          //! Returns the comment of the symbolic variable.
          const std::string& getComment(void) const;

          //! Returns the name of the symbolic variable.
          const std::string& getName(void) const;

          //! Returns the id of the symbolic variable. This id is unique.
          triton::usize getId(void) const;

          //! Returns the kind value of the symbolic variable.
          triton::uint64 getKindValue(void) const;

          //! Returns the size (in bits) of the symbolic variable.
          triton::uint32 getSize(void) const;

          //! Returns the concrete value (if exists) of the symbolic variable.
          triton::uint512 getConcreteValue(void) const;

          //! Sets the comment of the symbolic variable.
          void setComment(const std::string& comment);

          //! Sets the concrete value of the symbolic variable.
          void setConcreteValue(triton::uint512 value);
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

