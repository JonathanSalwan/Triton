//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_SMT2LIBSMTSYNTAX_HPP
#define TRITON_SMT2LIBSMTSYNTAX_HPP

#include <iostream>
#include "smt2lib.hpp"
#include "smt2libAbstractSyntax.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The SMT2-Lib namespace
  namespace smt2lib {
  /*!
   *  \ingroup triton
   *  \addtogroup smt2-lib
   *  @{
   */

    //! \module The pseudocode namespace
    namespace pseudocode {
    /*!
     *  \ingroup smt2lib
     *  \addtogroup pseudocode
     *  @{
     */

      //! SMT syntax.
      class SmtSyntax : public AbstractSyntax {
        public:
          //! Constructor.
          SmtSyntax();

          //! Destructor.
          ~SmtSyntax();

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstAbstractNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstAssertNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvaddNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvandNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvashrNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvdeclNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvlshrNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvmulNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvnandNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvnegNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvnorNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvnotNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvorNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvrolNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvrorNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsdivNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsgeNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsgtNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvshlNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsleNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsltNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsmodNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsremNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvsubNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvudivNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvugeNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvugtNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvuleNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvultNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvuremNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvxnorNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstBvxorNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstCompoundNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstConcatNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstDecimalNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstDeclareFunctionNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstDistinctNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstEqualNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstExtractNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstIteNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstLandNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstLetNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstLnotNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstLorNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstReferenceNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstStringNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstSxNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstVariableNode* node);

          //! Displays the node according to the pseudocode mode.
          std::ostream& display(std::ostream& stream, smtAstZxNode* node);
      };


    /*! @} End of pseudocode namespace */
    };
  /*! @} End of smt2lib namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SMT2LIBSMTSYNTAX_HPP */
