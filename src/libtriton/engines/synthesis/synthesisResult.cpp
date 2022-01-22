//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <triton/synthesisResult.hpp>



namespace triton {
  namespace engines {
    namespace synthesis {

      SynthesisResult::SynthesisResult() {
        this->input   = nullptr;
        this->output  = nullptr;
        this->success = false;
        this->time    = 0;
      }


      SynthesisResult::SynthesisResult(const SynthesisResult& other) {
        this->input   = other.input;
        this->output  = other.output;
        this->success = other.success;
        this->time    = other.time;
      }


      SynthesisResult& SynthesisResult::operator=(const SynthesisResult& other) {
        this->input   = other.input;
        this->output  = other.output;
        this->success = other.success;
        this->time    = other.time;

        return *this;
      }


      void SynthesisResult::setInput(const triton::ast::SharedAbstractNode& input) {
        this->input = input;
      }


      void SynthesisResult::setOutput(const triton::ast::SharedAbstractNode& output) {
        this->output = output;
      }


      void SynthesisResult::setTime(triton::usize ms) {
        this->time = ms;
      }


      const triton::ast::SharedAbstractNode SynthesisResult::getInput(void) {
        return this->input;
      }


      const triton::ast::SharedAbstractNode SynthesisResult::getOutput(void) {
        return this->output;
      }


      triton::usize SynthesisResult::getTime(void) {
        return this->time;
      }


      bool SynthesisResult::successful(void) {
        return this->success;
      }


      void SynthesisResult::setSuccess(bool flag) {
        this->success = flag;
      }

    }; /* synthesis namespace */
  }; /* engines namespace */
}; /* triton namespace */
