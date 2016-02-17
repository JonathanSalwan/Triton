//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <stdexcept>

#include <api.hpp>
#include <astRepresentation.hpp>



namespace triton {
  namespace ast {
    namespace representation {

      AstRepresentation::AstRepresentation() {
        /* Set the default representation */
        this->mode = triton::ast::representation::SMT_REPRESENTATION;

        /* Init representation interface */
        this->representation[triton::ast::representation::SMT_REPRESENTATION] = new triton::ast::representation::AstSmtRepresentation();
        this->representation[triton::ast::representation::PYTHON_REPRESENTATION] = new triton::ast::representation::AstPythonRepresentation();

        if (this->representation[triton::ast::representation::SMT_REPRESENTATION] == nullptr)
          throw std::runtime_error("triton::ast::representation::AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representation[triton::ast::representation::PYTHON_REPRESENTATION] == nullptr)
          throw std::runtime_error("triton::ast::representation::AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");
      }


      AstRepresentation::~AstRepresentation() {
        delete this->representation[triton::ast::representation::SMT_REPRESENTATION];
        delete this->representation[triton::ast::representation::PYTHON_REPRESENTATION];
      }


      triton::uint32 AstRepresentation::getMode(void) {
        return this->mode;
      }


      void AstRepresentation::setMode(triton::uint32 mode) {
        if (mode >= triton::ast::representation::LAST_REPRESENTATION)
          throw std::runtime_error("triton::ast::representation::AstRepresentation::setMode(): Invalid representation mode.");
        this->mode = mode;
      }


      std::ostream& AstRepresentation::print(std::ostream& stream, AbstractNode* node) {
        return this->representation[this->mode]->print(stream, node);
      }

    };
  };
};

