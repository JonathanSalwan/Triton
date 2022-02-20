//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_LIFTINGTODOT_HPP
#define TRITON_LIFTINGTODOT_HPP

#include <map>
#include <ostream>
#include <set>
#include <unordered_map>
#include <utility>

#include <triton/astContext.hpp>
#include <triton/dllexport.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/symbolicExpression.hpp>



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

    //! The Lifters namespace
    namespace lifters {
    /*!
     *  \ingroup engines
     *  \addtogroup lifters
     *  @{
     */

      //! \class LiftingToDot
      /*! \brief The lifting to Dot class. */
      class LiftingToDot {
        private:
          //! Reference to the context managing ast nodes.
          triton::ast::SharedAstContext astCtxt;

          //! Instance to the symbolic engine.
          triton::engines::symbolic::SymbolicEngine* symbolic;

          //! Unique id for some dot nodes
          triton::usize uniqueid;

          //! Information about AST extracted from symbolic expressions
          std::map<triton::ast::AbstractNode*, triton::engines::symbolic::SymbolicExpression*> information;

          //! List of symbolic expressions
          std::unordered_map<triton::usize, triton::engines::symbolic::SharedSymbolicExpression> expressions;

          //! List of dot edges
          std::set<std::pair<triton::usize, triton::usize>> edges;

          //! List of dot nodes
          std::set<std::pair<triton::usize, std::string>> nodes;

          //! Spreads information
          void spreadInformation(std::ostream& stream);

          //! Defines legend
          void defineLegend(std::ostream& stream);

          //! Iterates over nodes
          void iterateNodes(const triton::ast::SharedAbstractNode& root);

          //! Handles variable
          void handleVariable(const triton::ast::SharedAbstractNode& parent, const triton::ast::SharedAbstractNode& var);

        public:
          //! Constructor.
          TRITON_EXPORT LiftingToDot(const triton::ast::SharedAstContext& astCtxt, triton::engines::symbolic::SymbolicEngine* symbolic);

          //! Lifts an AST and all its references to Dot format.
          TRITON_EXPORT std::ostream& liftToDot(std::ostream& stream, const triton::ast::SharedAbstractNode& node);

          //! Lifts a symbolic expressions and all its references to Dot format.
          TRITON_EXPORT std::ostream& liftToDot(std::ostream& stream, const triton::engines::symbolic::SharedSymbolicExpression& expr);
      };

    /*! @} End of lifters namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_LIFTINGTODOT_HPP */
