//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include "api.hpp"
#include "astRepresentation.hpp"



namespace triton {
  namespace smt2lib {
    namespace representation {

      AstRepresentation::AstRepresentation() {
        /* Set the default representation */
        this->mode = triton::smt2lib::representation::SMT_REPRESENTATION;

        /* Init representation interface */
        this->representation[triton::smt2lib::representation::SMT_REPRESENTATION] = new triton::smt2lib::representation::AstSmtRepresentation();
        this->representation[triton::smt2lib::representation::PYTHON_REPRESENTATION] = new triton::smt2lib::representation::AstPythonRepresentation();

        if (this->representation[triton::smt2lib::representation::SMT_REPRESENTATION] == nullptr)
          throw std::runtime_error("triton::smt2lib::representation::AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representation[triton::smt2lib::representation::PYTHON_REPRESENTATION] == nullptr)
          throw std::runtime_error("triton::smt2lib::representation::AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");
      }


      AstRepresentation::~AstRepresentation() {
        delete this->representation[triton::smt2lib::representation::SMT_REPRESENTATION];
        delete this->representation[triton::smt2lib::representation::PYTHON_REPRESENTATION];
      }


      enum mode_e AstRepresentation::getMode(void) {
        return this->mode;
      }


      void AstRepresentation::setMode(enum mode_e mode) {
        if (mode >= triton::smt2lib::representation::LAST_REPRESENTATION)
          throw std::runtime_error("triton::smt2lib::representation::AstRepresentation::setMode(): Invalid representation mode.");
        this->mode = mode;
      }


      std::ostream& AstRepresentation::print(std::ostream& stream, smtAstAbstractNode* node) {
        return this->representation[this->mode]->print(stream, node);
      }

    };
  };
};

