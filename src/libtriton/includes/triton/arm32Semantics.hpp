//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#ifndef TRITON_ARM32SEMANTICS_H
#define TRITON_ARM32SEMANTICS_H

#include <triton/architecture.hpp>
#include <triton/dllexport.hpp>
#include <triton/instruction.hpp>
#include <triton/semanticsInterface.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/taintEngine.hpp>



//! The Triton namespace
namespace triton {
/*!
 *  \addtogroup triton
 *  @{
 */

  //! The Architecture namespace
  namespace arch {
  /*!
   *  \ingroup triton
   *  \addtogroup arch
   *  @{
   */

    //! The ARM namespace
    namespace arm {
    /*!
     *  \ingroup arch
     *  \addtogroup arm
     *  @{
     */

      //! The arm32 namespace
      namespace arm32 {
      /*!
       *  \ingroup arm
       *  \addtogroup arm32
       *  @{
       */

        /*! \class Arm32Semantics
            \brief The Arm32 ISA semantics. */
        class Arm32Semantics : public SemanticsInterface {
          private:
            //! Architecture API
            triton::arch::Architecture* architecture;

            //! Symbolic Engine API
            triton::engines::symbolic::SymbolicEngine* symbolicEngine;

            //! Taint Engine API
            triton::engines::taint::TaintEngine* taintEngine;

            //! The AST Context API
            triton::ast::SharedAstContext astCtxt;

          public:
            //! Constructor.
            TRITON_EXPORT Arm32Semantics(triton::arch::Architecture* architecture,
                                         triton::engines::symbolic::SymbolicEngine* symbolicEngine,
                                         triton::engines::taint::TaintEngine* taintEngine,
                                         const triton::ast::SharedAstContext& astCtxt);

            //! Builds the semantics of the instruction. Returns true if the instruction is supported.
            TRITON_EXPORT bool buildSemantics(triton::arch::Instruction& inst);

          private:
            //! Control flow semantics. Used to represent PC.
            void controlFlow_s(triton::arch::Instruction& inst);

            //! Control flow semantics. Used to represent PC.
            void controlFlow_s(triton::arch::Instruction& inst,
                               const triton::ast::SharedAbstractNode& cond,
                               triton::arch::OperandWrapper& dst);

            //! Creates a conditional node.
            triton::ast::SharedAbstractNode getCodeConditionAst(triton::arch::Instruction& inst);

            //! Gets the taint state (based on flags) of a conditional instruction.
            bool getCodeConditionTaintState(const triton::arch::Instruction& inst);

            //! Spreads taint based considering conditional execution.
            void spreadTaint(triton::arch::Instruction& inst,
                             const triton::ast::SharedAbstractNode& cond,
                             const triton::engines::symbolic::SharedSymbolicExpression& expr,
                             triton::arch::OperandWrapper& operand,
                             bool taint);

            /* Generic flags computation ------------------------------------- */

            //! The NF semantics.
            void nf_s(triton::arch::Instruction& inst,
                      const triton::ast::SharedAbstractNode& cond,
                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                      triton::arch::OperandWrapper& dst);

            //! The ZF semantics.
            void zf_s(triton::arch::Instruction& inst,
                      const triton::ast::SharedAbstractNode& cond,
                      const triton::engines::symbolic::SharedSymbolicExpression& parent,
                      triton::arch::OperandWrapper& dst);

            /* Specific flags computation ------------------------------------ */

            //! The CF semantics for the ADDS operation.
            void cfAdd_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         triton::arch::OperandWrapper& dst,
                         triton::ast::SharedAbstractNode& op1,
                         triton::ast::SharedAbstractNode& op2);

            //! The VF semantics for the ADDS operation.
            void vfAdd_s(triton::arch::Instruction& inst,
                         const triton::ast::SharedAbstractNode& cond,
                         const triton::engines::symbolic::SharedSymbolicExpression& parent,
                         triton::arch::OperandWrapper& dst,
                         triton::ast::SharedAbstractNode& op1,
                         triton::ast::SharedAbstractNode& op2);

            /* Instruction semantics ----------------------------------------- */

            //! The ADC semantics.
            void adc_s(triton::arch::Instruction& inst);

            //! The ADD semantics.
            void add_s(triton::arch::Instruction& inst);

            //! The BLX semantics.
            void blx_s(triton::arch::Instruction& inst);

            //! The BX semantics.
            void bx_s(triton::arch::Instruction& inst);
        };

      /*! @} End of arm32 namespace */
      };
    /*! @} End of arm namespace */
    };
  /*! @} End of arch namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_ARM32SEMANTICS_H */
