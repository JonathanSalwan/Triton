//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICVARIABLE_H
#define TRITON_SYMBOLICVARIABLE_H

#include <string>

#include "symbolicEnums.hpp"
#include "tritonTypes.hpp"



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

          //! The comment of the symbolic variable.
          std::string symVarComment;

          //! The name of the symbolic variable. \sa TRITON_SYMVAR_NAME
          std::string symVarName;

          //! The id of the symbolic variable. This id is unique.
          triton::__uint symVarId;

          //! The kind value of the symbolic variable.
          /*!
            \brief If the symbolic varialbe is a triton::engines::symbolic::REG, this value contains the register ID.
            \biref If the symbolic varialbe is a triton::engines::symbolic::MEM, this value contains the memory access' address.
          */
          triton::__uint symVarKindValue;

          //! The size (in bits) of the symbolic variable.
          triton::uint32 symVarSize;

          //! The concrete value of the symbolic variable.
          triton::uint512 symVarConcreteValue;

        public:

          //! Constructor.
          SymbolicVariable(symkind_e kind, triton::__uint kindValue, triton::__uint id, triton::uint32 size, const std::string& comment, triton::uint512 concreteValue=0);

          //! Constructor by copy.
          SymbolicVariable(const SymbolicVariable &copy);

          //! Destructore.
          ~SymbolicVariable();

          //! Returns the symbolic variable kind. \sa triton::engines::symbolic::symkind_e.
          symkind_e getSymVarKind(void) const;

          //! Returns the comment of the symbolic variable.
          const std::string& getSymVarComment(void) const;

          //! Returns the name of the symbolic variable.
          const std::string& getSymVarName(void) const;

          //! Returns the id of the symbolic variable. This id is unique.
          triton::__uint getSymVarId(void) const;

          //! Returns the kind value of the symbolic variable.
          triton::__uint getSymVarKindValue(void) const;

          //! Returns the size (in bits) of the symbolic variable.
          triton::uint32 getSymVarSize(void) const;

          //! Returns the concrete value (if exists) of the symbolic variable.
          triton::uint512 getConcreteValue(void) const;

          //! Sets the comment of the symbolic variable.
          void setSymVarComment(const std::string& comment);

          //! Sets the concrete value of the symbolic variable.
          void setSymVarConcreteValue(triton::uint512 value);
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

