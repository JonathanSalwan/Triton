//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef ORACLEENTRY_HPP
#define ORACLEENTRY_HPP

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
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

    //! The Synthesis namespace
    namespace synthesis {
    /*!
     *  \ingroup engines
     *  \addtogroup synthesis
     *  @{
     */

      //! \class ConstantEntry
      /*! \brief Entry of the oracle table for constant synthesis. */
      class ConstantEntry {
        public:
          //! AST operator
          triton::ast::SharedAbstractNode op;

          //! Constant position in the AST
          triton::uint8 position;

          //! Constructor
          TRITON_EXPORT ConstantEntry(triton::uint8 position, const triton::ast::SharedAbstractNode& op)
            : position(position), op(op) {
          };
      };

      //! \class UnaryEntry
      /*! \brief Entry of the oracle table for unary operators synthesis. */
      class UnaryEntry {
        public:
          //! Size of the oracle
          triton::uint32 bits;

          //! Value of x
          triton::uint64 x;

          //! Result of x <op> y
          triton::uint64 r;

          //! Constructor
          TRITON_EXPORT UnaryEntry(triton::uint8 bits, triton::uint64 x, triton::uint64 r)
            : bits(bits), x(x), r(r) {
          };
      };

      //! \class BinaryEntry
      /*! \brief Entry of the oracle table for binary operators synthesis. */
      class BinaryEntry {
        public:
          //! Size of the oracle
          triton::uint32 bits;

          //! Value of x
          triton::uint64 x;

          //! Value of y
          triton::uint64 y;

          //! Result of x <op> y
          triton::uint64 r;

          //! Constructor
          TRITON_EXPORT BinaryEntry(triton::uint8 bits, triton::uint64 x, triton::uint64 y, triton::uint64 r)
            : bits(bits), x(x), y(y), r(r) {
          };
      };

    /*! @} End of synthesis namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* ORACLEENTRY_HPP */
