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
    namespace representations {

      AstRepresentation::AstRepresentation() {
        /* Set the default representation */
        this->mode = triton::ast::representations::SMT_REPRESENTATION;

        /* Init representations interface */
        this->representations[triton::ast::representations::SMT_REPRESENTATION] = new triton::ast::representations::AstSmtRepresentation();
        this->representations[triton::ast::representations::PYTHON_REPRESENTATION] = new triton::ast::representations::AstPythonRepresentation();

        if (this->representations[triton::ast::representations::SMT_REPRESENTATION] == nullptr)
          throw std::runtime_error("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representations[triton::ast::representations::PYTHON_REPRESENTATION] == nullptr)
          throw std::runtime_error("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");
      }


      AstRepresentation::~AstRepresentation() {
        delete this->representations[triton::ast::representations::SMT_REPRESENTATION];
        delete this->representations[triton::ast::representations::PYTHON_REPRESENTATION];
      }


      triton::uint32 AstRepresentation::getMode(void) const {
        return this->mode;
      }


      void AstRepresentation::setMode(triton::uint32 mode) {
        if (mode >= triton::ast::representations::LAST_REPRESENTATION)
          throw std::runtime_error("AstRepresentation::setMode(): Invalid representation mode.");
        this->mode = mode;
      }


      std::ostream& AstRepresentation::print(std::ostream& stream, AbstractNode* node) {
        return this->representations[this->mode]->print(stream, node);
      }

    };
  };
};

