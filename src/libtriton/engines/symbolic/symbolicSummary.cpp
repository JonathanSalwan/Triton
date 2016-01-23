//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <api.hpp>
#include <symbolicSummary.hpp>

/*
 *
 * /!\ Still experimental /!\
 *
 */



namespace triton {
  namespace engines {
    namespace symbolic {

      /* Decimal Summaries */
      std::map<triton::uint128, triton::smt2lib::smtAstAbstractNode*> decimalSummaries;

    }; /* symbolic namespace */
  }; /* engines namespace */
}; /*triton namespace */

