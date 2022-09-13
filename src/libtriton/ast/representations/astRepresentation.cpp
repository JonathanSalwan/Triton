//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

#include <new>
#include <memory>

#include <triton/astPcodeRepresentation.hpp>
#include <triton/astPythonRepresentation.hpp>
#include <triton/astRepresentation.hpp>
#include <triton/astSmtRepresentation.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace ast {
    namespace representations {

      AstRepresentation::AstRepresentation() {
        /* Set the default representation */
        this->mode = SMT_REPRESENTATION;

        /* Init representations interface */
        this->representations[SMT_REPRESENTATION]    = std::unique_ptr<AstSmtRepresentation>(new(std::nothrow) AstSmtRepresentation());
        this->representations[PYTHON_REPRESENTATION] = std::unique_ptr<AstPythonRepresentation>(new(std::nothrow) AstPythonRepresentation());
        this->representations[PCODE_REPRESENTATION]  = std::unique_ptr<AstPcodeRepresentation>(new(std::nothrow) AstPcodeRepresentation());

        if (this->representations[SMT_REPRESENTATION] == nullptr)
          throw triton::exceptions::AstRepresentation("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representations[PYTHON_REPRESENTATION] == nullptr)
          throw triton::exceptions::AstRepresentation("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representations[PCODE_REPRESENTATION] == nullptr)
          throw triton::exceptions::AstRepresentation("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");
      }


      AstRepresentation::AstRepresentation(const AstRepresentation& other)
      : AstRepresentation() {
        this->mode = other.mode;
      }


      AstRepresentation& AstRepresentation::operator=(const AstRepresentation& other) {
        this->mode = other.mode;
        return *this;
      }


      triton::ast::representations::mode_e AstRepresentation::getMode(void) const {
        return this->mode;
      }


      void AstRepresentation::setMode(triton::ast::representations::mode_e mode) {
        if (mode >= triton::ast::representations::LAST_REPRESENTATION)
          throw triton::exceptions::AstRepresentation("AstRepresentation::setMode(): Invalid representation mode.");
        this->mode = mode;
      }


      std::ostream& AstRepresentation::print(std::ostream& stream, AbstractNode* node) {
        return this->representations[this->mode]->print(stream, node);
      }

    };
  };
};
