//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICVARIABLE_H
#define TRITON_SYMBOLICVARIABLE_H

#include <string>
#include "symbolicExpression.hpp"
#include "tritonTypes.hpp"

/*! Defines the name of a symbolic variable. */
#define SYMVAR_NAME "SymVar_"

/*! Defines the size of a symbolic variable' name. */
#define SYMVAR_NAME_SIZE (sizeof(SYMVAR_NAME) - 1)



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The Engines namespace
  namespace engines {
  /*!
   *  \ingroup triton
   *  \addtogroup engines
   *  @{
   */

    //! \module The Symbolic Execution namespace
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
          symkind_e symVarKind;

          //! The symbolic variable's comment.
          std::string symVarComment;

          //! The symbolic variable's name. \sa SYMVAR_NAME
          std::string symVarName;

          //! The symbolic variable's id. This id is unique.
          triton::__uint symVarId;

          //! The symbolic variable's kind value.
          /*!
            \brief If the symbolic varialbe is a triton::engines::symbolic::REG, this value contains the register ID.
            \biref If the symbolic varialbe is a triton::engines::symbolic::MEM, this value contains the memory access' address.
          */
          triton::__uint symVarKindValue;

          //! The symbolic variable's size.
          triton::uint32 symVarSize;

          //! The symbolic variable's concrete value.
          triton::uint128 symVarConcreteValue;

          //! True if the symbolic variable has a concrete value.
          bool symVarHasConcreteValue;

        public:

          //! Constructor.
          SymbolicVariable(symkind_e kind, triton::__uint kindValue, triton::__uint id, triton::uint32 size, std::string comment, triton::uint128 concreteValue);

          //! Constructor.
          SymbolicVariable(symkind_e kind, triton::__uint kindValue, triton::__uint id, triton::uint32 size, std::string comment);

          //! Constructor by copy.
          SymbolicVariable(const SymbolicVariable &copy);

          //! Destructore.
          ~SymbolicVariable();

          //! Returns the symbolic variable kind. \sa triton::engines::symbolic::symkind_e.
          symkind_e getSymVarKind(void);

          //! Returns the symbolic variable's comment.
          std::string getSymVarComment(void);

          //! Returns the symbolic variable's name.
          std::string getSymVarName(void);

          //! Returns the symbolic variable's id. This id is unique.
          triton::__uint getSymVarId(void);

          //! Returns the symbolic variable's kind value.
          triton::__uint getSymVarKindValue(void);

          //! Returns the symbolic variable's size.
          triton::uint32 getSymVarSize(void);

          //! Returns the symbolic variable's concrete value if exists.
          triton::uint128 getConcreteValue(void);

          //! Returns true if the symbolic variable has a concrete value.
          bool hasConcreteValue(void);

          //! Sets the symbolic variable's concrete value.
          void setSymVarConcreteValue(triton::uint128 value);

      };

      //! Displays a symbolic variable.
      std::ostream &operator<<(std::ostream &stream, SymbolicVariable symVar);

      //! Displays a symbolic variable.
      std::ostream &operator<<(std::ostream &stream, SymbolicVariable* symVar);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICVARIABLE_H */

