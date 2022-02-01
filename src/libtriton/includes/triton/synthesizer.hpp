//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_SYNTHESIZER_HPP
#define TRITON_SYNTHESIZER_HPP

#include <array>
#include <deque>
#include <map>

#include <triton/astContext.hpp>
#include <triton/dllexport.hpp>
#include <triton/oracleEntry.hpp>
#include <triton/solverEngine.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/synthesisResult.hpp>
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

      //! The Synthesis namespace
      namespace oracles {
      /*!
       *  \ingroup synthesis
       *  \addtogroup oracles
       *  @{
       */

        //! The oracle table for unary operators. Each entry is a UnaryEntry object.
        extern std::map<triton::ast::ast_e, std::array<UnaryEntry, 40>> unopTable;

        //! The oracle table for binary operators. Each entry is a BinaryEntry object.
        extern std::map<triton::ast::ast_e, std::array<BinaryEntry, 40>> binopTable;

      /*! @} End of oracle namespace */
      };

      //! \class Synthesizer
      /*! \brief The Synthesizer engine class. */
      class Synthesizer {
        private:
          //! Map of subexpr hash to their new symbolic variable
          std::map<triton::uint512, triton::ast::SharedAbstractNode> hash2var;

          //! Map of symbolic variables to their synthesized node
          std::map<triton::ast::SharedAbstractNode, triton::ast::SharedAbstractNode> var2expr;

          //! An instance of a solver engine to solver queries
          triton::engines::solver::SolverEngine solver;

          //! An instance of a symbolic engine to create symbolic variable
          triton::engines::symbolic::SymbolicEngine* symbolic;

          //! Synthesize a given node that contains one variable (constant synthesizing)
          bool constantSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result);

          //! Synthesize a given node that two variables (opaque constant synthesizing)
          bool opaqueConstantSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result);

          //! Synthesize a given node that contains one variable with one operator
          bool unaryOperatorSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result);

          //! Synthesize a given node that contains two variables with one operator
          bool binaryOperatorSynthesis(const std::deque<triton::ast::SharedAbstractNode>& vars, const triton::ast::SharedAbstractNode& node, SynthesisResult& result);

          //! Synthesize children expression
          bool childrenSynthesis(const triton::ast::SharedAbstractNode& node, bool constant, bool opaque, SynthesisResult& result);

          //! Do the synthesis
          bool do_synthesize(const triton::ast::SharedAbstractNode& node, bool constant, bool opaque, SynthesisResult& result);

          //! Symbolize sub epxressions
          triton::ast::SharedAbstractNode symbolizeSubExpression(const triton::ast::SharedAbstractNode& node, SynthesisResult& tmpResult);

          //! Substitute all sub epxressions
          void substituteSubExpression(const triton::ast::SharedAbstractNode& node);

        public:
          //! Constructor.
          TRITON_EXPORT Synthesizer(triton::engines::symbolic::SymbolicEngine* symbolic);

          //! Synthesizes a given node. If `constant` is true, perform a constant synthesis. If `opaque` is true, perform opaque constant synthesis. If `subexpr` is true, analyze children AST.
          TRITON_EXPORT SynthesisResult synthesize(const triton::ast::SharedAbstractNode& node, bool constant=true, bool subexpr=true, bool opaque=false);
      };

    /*! @} End of synthesis namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYNTHESIZER_HPP */
