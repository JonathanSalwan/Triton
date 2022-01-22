//
//  This program is under the terms of the BSD License.
//  Jonathan Salwan - 2022-01-22
//

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

      class OracleEntry {
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
          TRITON_EXPORT OracleEntry(triton::uint8 bits, triton::uint64 x, triton::uint64 y, triton::uint64 r)
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
