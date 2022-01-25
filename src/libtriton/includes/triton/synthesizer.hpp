//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef SYNTHESIZER_HPP
#define SYNTHESIZER_HPP

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

      //! The oracle table. Each entry is an OracleEntry object.
      extern std::map<triton::ast::ast_e, std::array<OracleEntry, 40>> oracleTable;

      //! \class Synthesizer
      /*! \brief The Synthesizer engine class. */
      class Synthesizer {
        private:
          //! An instance of a solver engine to solver queries
          triton::engines::solver::SolverEngine solver;

          //! An instance of a symbolic engine to create symbolic variable
          triton::engines::symbolic::SymbolicEngine* symbolic;

          //! Synthesize a given node that contains one variable (constant synthesizing)
          bool constantSynthesis(const triton::ast::SharedAstContext& actx, const std::deque<triton::ast::SharedAbstractNode>& vars,
                                 const triton::ast::SharedAbstractNode& node, SynthesisResult& result);

          //! Synthesize a given node that contains two variables with one operator
          bool binaryOperatorSynthesis(const triton::ast::SharedAstContext& actx, const std::deque<triton::ast::SharedAbstractNode>& vars,
                                       const triton::ast::SharedAbstractNode& node, SynthesisResult& result);

        public:
          //! Constructor.
          TRITON_EXPORT Synthesizer(triton::engines::symbolic::SymbolicEngine* symbolic);

          //! Synthesize a given node
          TRITON_EXPORT SynthesisResult synthesize(const triton::ast::SharedAbstractNode& node, bool constant=true);
      };

    /*! @} End of synthesis namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* SYNTHESIZER_HPP */
