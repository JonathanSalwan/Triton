//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_SYMBOLICEXPRESSION_H
#define TRITON_SYMBOLICEXPRESSION_H

#include <string>

#include <tritonast/nodes.hpp>
#include <triton/memoryAccess.hpp>
#include <triton/register.hpp>
#include <triton/symbolicEnums.hpp>
#include <tritoncore/types.hpp>
#include <triton/symbolicValue.hpp>



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

      //! \class SymbolicExpression
      /*! \brief The symbolic expression class */
      class SymbolicExpression: public SymbolicValue {

        protected:
          //! The origin memory address if `kind` is equal to `triton::engines::symbolic::MEM`, invalid memory otherwise.
          triton::arch::MemoryAccess originMemory;

          //! The origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          triton::arch::Register originRegister;

        public:
          //! True if the symbolic expression is tainted.
          bool isTainted;

          //! Returns the id as string of the symbolic expression according the mode of the AST representation.
          std::string getFormattedId(void) const;

          //! Returns the comment as string of the symbolic expression according the mode of the AST representation.
          std::string getFormattedComment(void) const;

          //! Returns the origin memory access if `kind` is equal to `triton::engines::symbolic::MEM`, invalid memory otherwise.
          const triton::arch::MemoryAccess& getOriginMemory(void) const;

          //! Returns the origin register if `kind` is equal to `triton::engines::symbolic::REG`, `REG_INVALID` otherwise.
          const triton::arch::Register& getOriginRegister(void) const;

          //! Sets the origin memory acccess.
          void setOriginMemory(const triton::arch::MemoryAccess& mem);

          //! Sets the origin register.
          void setOriginRegister(const triton::arch::Register& reg);

          //! Constructor.
          SymbolicExpression(triton::ast::SharedAbstractNode const& expr, triton::usize id, symkind_e kind, const std::string& comment="");
      };

      //! Displays a symbolic expression.
      std::ostream& operator<<(std::ostream& stream, const SymbolicExpression& symExpr);

      //! Displays a symbolic expression.
      std::ostream& operator<<(std::ostream& stream, const SymbolicExpression* symExpr);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };

  using SharedSymbolicExpression = std::shared_ptr<triton::engines::symbolic::SymbolicExpression>;

/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICEXPRESSION_H */

