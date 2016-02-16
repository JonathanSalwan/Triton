//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TRITON_ASTPYTHONREPRESENTATION_HPP
#define TRITON_ASTPYTHONREPRESENTATION_HPP

#include <iostream>
#include "astRepresentationInterface.hpp"
#include "ast.hpp"



//! \module The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! \module The SMT2-Lib namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    //! \module The representation namespace
    namespace representation {
    /*!
     *  \ingroup ast
     *  \addtogroup representation
     *  @{
     */

      //! Python representation.
      class AstPythonRepresentation : public AstRepresentationInterface {
        public:
          //! Constructor.
          AstPythonRepresentation();

          //! Destructor.
          ~AstPythonRepresentation();

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstAbstractNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstAssertNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvaddNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvandNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvashrNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvdeclNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvlshrNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvmulNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvnandNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvnegNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvnorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvnotNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvrolNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvrorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsdivNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsgeNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsgtNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvshlNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsleNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsltNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsmodNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsremNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvsubNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvudivNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvugeNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvugtNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvuleNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvultNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvuremNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvxnorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstBvxorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstCompoundNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstConcatNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstDecimalNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstDeclareFunctionNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstDistinctNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstEqualNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstExtractNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstIteNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstLandNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstLetNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstLnotNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstLorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstReferenceNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstStringNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstSxNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstVariableNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::smtAstZxNode* node);
      };


    /*! @} End of representation namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTPYTHONREPRESENTATION_HPP */
