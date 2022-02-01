//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_ORACLEENTRY_HPP
#define TRITON_ORACLEENTRY_HPP

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

          /*! Constant position in the AST
           * \brief
           * Example 1: c - x -> 0
           * Example 2: x - c -> 1
           */
          triton::uint8 position;

          //! Constructor
          TRITON_EXPORT ConstantEntry(triton::uint8 position, const triton::ast::SharedAbstractNode& op)
            : op(op), position(position) {
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

      /*! \class OpEncoding
       * \brief This class is used to encode operators and variables ordering.
       * \brief Example 1: ((a + b) * a)     -> OpEncoding<2>({BVADD, BVMUL}, {0, 1, 0})
       * \brief Example 2: (a + (b * a))     -> OpEncoding<2>({BVMUL, BVADD}, {1, 0, 0})
       * \brief Example 3: (a + b) * (a - b) -> OpEncoding<3>({BVMUL, BVADD, BVSUB}, {0, 1, 0, 1})
       *
       * Example for a trinary operator like bvadd(bvmul(x, x), y):
       * {
       *   OpEncoding<2>({triton::ast::BVADD_NODE, triton::ast::BVMUL_NODE}, {0, 0, 1}), {
       *     BinaryEntry(8, 0x74, 0xe7, 0x77), BinaryEntry(16, 0x04c3, 0xd4d4, 0x815d), ...
       *     BinaryEntry(8, 0x98, 0x13, 0x53), BinaryEntry(16, 0x46dd, 0xc2dd, 0x5da6), ...
       *     BinaryEntry(8, 0x3f, 0xf4, 0x75), BinaryEntry(16, 0xa6b7, 0xac75, 0x8346), ...
       *     BinaryEntry(8, 0x26, 0xf0, 0x94), BinaryEntry(16, 0x31cd, 0x33c5, 0x51ee), ...
       *     BinaryEntry(8, 0x8e, 0x5e, 0x22), BinaryEntry(16, 0x77b8, 0xbba1, 0x4fe1), ...
       *     BinaryEntry(8, 0x48, 0x7c, 0xbc), BinaryEntry(16, 0x1c89, 0xed45, 0x2e96), ...
       *     BinaryEntry(8, 0x9f, 0x7b, 0x3c), BinaryEntry(16, 0xbfcc, 0xd906, 0xe396), ...
       *     BinaryEntry(8, 0x45, 0xe3, 0x7c), BinaryEntry(16, 0xd200, 0xb90c, 0xb90c), ...
       *     BinaryEntry(8, 0x16, 0x0a, 0xee), BinaryEntry(16, 0xd946, 0x9d22, 0x5c46), ...
       *     BinaryEntry(8, 0xed, 0x59, 0xc2), BinaryEntry(16, 0x1c7b, 0x810c, 0xa425), ...
       *   }
       * }
       */
      template<std::size_t N>
      class OpEncoding {
        public:
          /*! Ordering of operators
           * \brief
           * Example 1: ((a + b) * a) -> {BVADD, BVMUL}
           * Example 2: (a + (b * a)) -> {BVMUL, BVADD}
           * Example 3: (a + (b + a)) -> {BVADD, BVADD}
           */
          std::array<triton::ast::ast_e, N> ops;

          /*! Ordering of variables
           * \brief
           * Example 1: ((a + b) * a) -> {0, 1, 0}
           * Example 2: ((a + a) * a) -> {0, 0, 0}
           * Example 3: ((b + b) * a) -> {1, 1, 0}
           * Example 4: ((b + a) * b) -> {1, 0, 1}
           * Example 4: (b + (a * b)) -> {0, 1, 1}
           */
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

#endif /* TRITON_ORACLEENTRY_HPP */
