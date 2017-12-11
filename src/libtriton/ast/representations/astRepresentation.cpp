//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <new>
#include <memory>

#include <triton/astRepresentation.hpp>
#include <triton/exceptions.hpp>



namespace triton {
  namespace ast {
    namespace representations {

      AstRepresentation::AstRepresentation() {
        /* Set the default representation */
        this->mode = triton::ast::representations::SMT_REPRESENTATION;

        /* Init representations interface */
        this->representations[triton::ast::representations::SMT_REPRESENTATION] = std::unique_ptr<triton::ast::representations::AstSmtRepresentation>(new(std::nothrow) triton::ast::representations::AstSmtRepresentation());
        this->representations[triton::ast::representations::PYTHON_REPRESENTATION] = std::unique_ptr<triton::ast::representations::AstPythonRepresentation>(new(std::nothrow) triton::ast::representations::AstPythonRepresentation());

        if (this->representations[triton::ast::representations::SMT_REPRESENTATION] == nullptr)
          throw triton::exceptions::AstRepresentation("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representations[triton::ast::representations::PYTHON_REPRESENTATION] == nullptr)
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


      triton::uint32 AstRepresentation::getMode(void) const {
        return this->mode;
      }


      void AstRepresentation::setMode(triton::uint32 mode) {
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

