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
          //! \brief Example: bvadd
          triton::ast::SharedAbstractNode op;

          //! Constant position in the AST
          //! \brief Example 1: c - x -> 0
          //! \brief Example 2: x - c -> 1
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

          //! Result of <op>(x)
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

      //! \class OpEncoding
      /*! \brief This class is used to encode operators and variables ordering. */
      /*! \brief Example 1: ((a + b) * a)     -> OpEncoding<2>({BVADD, BVMUL}, {0, 1, 0})           */
      /*! \brief Example 2: (a + (b * a))     -> OpEncoding<2>({BVMUL, BVADD}, {1, 0, 0})           */
      /*! \brief Example 3: (a + b) * (a - b) -> OpEncoding<3>({BVMUL, BVADD, BVSUB}, {0, 1, 0, 1}) */
      template<std::size_t N>
      class OpEncoding {
        public:
          //! Ordering of operators
          /*! \brief Example 1: ((a + b) * a) -> {BVADD, BVMUL} */
          /*! \brief Example 2: (a + (b * a)) -> {BVMUL, BVADD} */
          /*! \brief Example 3: (a + (b + a)) -> {BVADD, BVADD} */
          std::array<triton::ast::ast_e, N> ops;

          //! Ordering of variables
          /*! \brief Example 1: ((a + b) * a) -> {0, 1, 0} */
          /*! \brief Example 2: ((a + a) * a) -> {0, 0, 0} */
          /*! \brief Example 3: ((b + b) * a) -> {1, 1, 0} */
          /*! \brief Example 4: ((b + a) * b) -> {1, 0, 1} */
          /*! \brief Example 4: (b + (a * b)) -> {0, 1, 1} */
          std::array<triton::uint8, N + 1> vars;

          //! Constructor
          OpEncoding(std::array<triton::ast::ast_e, N> ops, std::array<triton::uint8, N + 1> vars)
            : ops(ops), vars(vars) {
          }
      };

      //! Operator implementation in order to use OpEncoding as key in a std::map.
      template<std::size_t N>
      bool operator<(const OpEncoding<N>& obj1, const OpEncoding<N>& obj2) {
        return (&obj1 < &obj2);
      }

    /*! @} End of synthesis namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* ORACLEENTRY_HPP */
