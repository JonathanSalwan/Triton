//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include "api.hpp"
#include "smt2libPseudocode.hpp"



namespace triton {
  namespace smt2lib {
    namespace pseudocode {

      Pseudocode::Pseudocode() {
        /* Set the default syntax */
        this->mode = triton::smt2lib::pseudocode::SMT_SYNTAX;

        /* Init syntax interface */
        this->syntax[triton::smt2lib::pseudocode::SMT_SYNTAX] = new triton::smt2lib::pseudocode::SmtSyntax();
        this->syntax[triton::smt2lib::pseudocode::PYTHON_SYNTAX] = new triton::smt2lib::pseudocode::PythonSyntax();

        if (this->syntax[triton::smt2lib::pseudocode::SMT_SYNTAX] == nullptr)
          throw std::runtime_error("triton::smt2lib::pseudocode::Pseudocode::Pseudocode(): Cannot allocate a new syntax instance.");

        if (this->syntax[triton::smt2lib::pseudocode::PYTHON_SYNTAX] == nullptr)
          throw std::runtime_error("triton::smt2lib::pseudocode::Pseudocode::Pseudocode(): Cannot allocate a new syntax instance.");
      }


      Pseudocode::~Pseudocode() {
        delete this->syntax[triton::smt2lib::pseudocode::SMT_SYNTAX];
        delete this->syntax[triton::smt2lib::pseudocode::PYTHON_SYNTAX];
      }


      enum mode_e Pseudocode::getKind(void) {
        return this->mode;
      }


      void Pseudocode::setMode(enum mode_e mode) {
        if (mode >= triton::smt2lib::pseudocode::LAST_SYNTAX)
          throw std::runtime_error("triton::smt2lib::pseudocode::Pseudocode::setMode(): Invalid syntax mode.");
        this->mode = mode;
      }


      std::ostream& Pseudocode::display(std::ostream& stream, smtAstAbstractNode* node) {
        return this->syntax[this->mode]->display(stream, node);
      }

    };
  };
};

