//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ASTPYTHONREPRESENTATION_HPP
#define TRITON_ASTPYTHONREPRESENTATION_HPP

#include <iostream>                               // for ostream
#include <triton/astRepresentationInterface.hpp>  // for AstRepresentationIn...


//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The AST namespace
  namespace ast {
  /*!
   *  \ingroup triton
   *  \addtogroup ast
   *  @{
   */

    class AbstractNode;
    class AssertNode;
    class BvNode;
    class BvaddNode;
    class BvandNode;
    class BvashrNode;
    class BvdeclNode;
    class BvlshrNode;
    class BvmulNode;
    class BvnandNode;
    class BvnegNode;
    class BvnorNode;
    class BvnotNode;
    class BvorNode;
    class BvrolNode;
    class BvrorNode;
    class BvsdivNode;
    class BvsgeNode;
    class BvsgtNode;
    class BvshlNode;
    class BvsleNode;
    class BvsltNode;
    class BvsmodNode;
    class BvsremNode;
    class BvsubNode;
    class BvudivNode;
    class BvugeNode;
    class BvugtNode;
    class BvuleNode;
    class BvultNode;
    class BvuremNode;
    class BvxnorNode;
    class BvxorNode;
    class CompoundNode;
    class ConcatNode;
    class DecimalNode;
    class DeclareFunctionNode;
    class DistinctNode;
    class EqualNode;
    class ExtractNode;
    class IteNode;
    class LandNode;
    class LetNode;
    class LnotNode;
    class LorNode;
    class ReferenceNode;
    class StringNode;
    class SxNode;
    class VariableNode;
    class ZxNode;

    //! The Representations namespace
    namespace representations {
    /*!
     *  \ingroup ast
     *  \addtogroup representations
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
          std::ostream& print(std::ostream& stream, triton::ast::AbstractNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::AssertNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvaddNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvandNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvashrNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvdeclNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvlshrNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvmulNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvnandNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvnegNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvnorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvnotNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvrolNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvrorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsdivNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsgeNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsgtNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvshlNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsleNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsltNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsmodNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsremNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvsubNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvudivNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvugeNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvugtNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvuleNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvultNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvuremNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvxnorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::BvxorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::CompoundNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::ConcatNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::DecimalNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::DeclareFunctionNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::DistinctNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::EqualNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::ExtractNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::IteNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::LandNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::LetNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::LnotNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::LorNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::ReferenceNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::StringNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::SxNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::VariableNode* node);

          //! Displays the node according to the representation mode.
          std::ostream& print(std::ostream& stream, triton::ast::ZxNode* node);
      };


    /*! @} End of representations namespace */
    };
  /*! @} End of ast namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ASTPYTHONREPRESENTATION_HPP */
