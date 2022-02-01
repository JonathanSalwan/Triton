//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#ifndef TRITON_SYNTHESISRESULT_HPP
#define TRITON_SYNTHESISRESULT_HPP

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

      //! \class SynthesisResult
      /*! \brief The SynthesisResult engine class. */
      class SynthesisResult {
        private:
          //! True if the input node has been synthesized successfully.
          bool success;

          //! The input node.
          triton::ast::SharedAbstractNode input;

          //! The output node. This node is the same as the `input` one if success is `False`, otherwise it returns the synthesized one.
          triton::ast::SharedAbstractNode output;

          //! Time (milliseconds) of the synthesizing
          triton::usize time;

        public:
          //! Constructor.
          TRITON_EXPORT SynthesisResult();

          //! Constructor by copy.
          TRITON_EXPORT SynthesisResult(const SynthesisResult& other);

          //! Copies a SynthesisResult.
          SynthesisResult& operator=(const SynthesisResult& other);

          //! Sets the input node
          TRITON_EXPORT void setInput(const triton::ast::SharedAbstractNode& input);

          //! Sets the output node
          TRITON_EXPORT void setOutput(const triton::ast::SharedAbstractNode& output);

          //! Sets the time
          TRITON_EXPORT void setTime(triton::usize ms);

          //! Sets the success flag.
          TRITON_EXPORT void setSuccess(bool value);

          //! Gets the input node
          TRITON_EXPORT const triton::ast::SharedAbstractNode getInput(void);

          //! Gets the output node
          TRITON_EXPORT const triton::ast::SharedAbstractNode getOutput(void);

          //! Gets the time of the synthesizing
          TRITON_EXPORT triton::usize getTime(void);

          //! Returns True the input node has been synthesized successfully.
          TRITON_EXPORT bool successful(void);
      };

    /*! @} End of synthesis namespace */
    };
  /*! @} End of engines namespace */
  };
/*! @} End of triton namespace */
};

#endif /* TRITON_SYNTHESISRESULT_HPP */
