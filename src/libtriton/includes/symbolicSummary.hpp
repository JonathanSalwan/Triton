//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SYMBOLICSUMMARY_H
#define TRITON_SYMBOLICSUMMARY_H

#include <list>

#include "smt2lib.hpp"
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

      //! Decimal Summaries
      extern std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> decimalSummaries;

      //! Bv Summaries
      extern std::map<std::vector<triton::smt2lib::smtAstAbstractNode*>, triton::smt2lib::smtAstAbstractNode*> bvSummaries;

      //! Browses into summaries
      triton::smt2lib::smtAstAbstractNode* browseSummaries(triton::smt2lib::smtAstAbstractNode* node);

    /*! @} End of symbolic namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYMBOLICSUMMARY_H */

