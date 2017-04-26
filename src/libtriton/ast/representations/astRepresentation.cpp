//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <iosfwd>                                 // for ostream
#include <new>                                    // for nothrow, operator new
#include <triton/astRepresentation.hpp>           // for AstRepresentation
#include <triton/exceptions.hpp>                  // for AstRepresentation
#include "triton/astPythonRepresentation.hpp"     // for AstPythonRepresenta...
#include "triton/astRepresentationInterface.hpp"  // for AstRepresentationIn...
#include "triton/astSmtRepresentation.hpp"        // for AstSmtRepresentation
#include "triton/tritonTypes.hpp"                 // for uint32


namespace triton {
  namespace ast {
    class AbstractNode;
    namespace representations {

      /* External access to the AST representation API */
      AstRepresentation astRepresentation = AstRepresentation();


      AstRepresentation::AstRepresentation() {
        /* Set the default representation */
        this->mode = triton::ast::representations::SMT_REPRESENTATION;

        /* Init representations interface */
        this->representations[triton::ast::representations::SMT_REPRESENTATION] = new(std::nothrow) triton::ast::representations::AstSmtRepresentation();
        this->representations[triton::ast::representations::PYTHON_REPRESENTATION] = new(std::nothrow) triton::ast::representations::AstPythonRepresentation();

        if (this->representations[triton::ast::representations::SMT_REPRESENTATION] == nullptr)
          throw triton::exceptions::AstRepresentation("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");

        if (this->representations[triton::ast::representations::PYTHON_REPRESENTATION] == nullptr)
          throw triton::exceptions::AstRepresentation("AstRepresentation::AstRepresentation(): Cannot allocate a new representation instance.");
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
          throw triton::exceptions::AstRepresentation("AstRepresentation::setMode(): Invalid representation mode.");
        this->mode = mode;
      }


      std::ostream& AstRepresentation::print(std::ostream& stream, AbstractNode* node) {
        return this->representations[this->mode]->print(stream, node);
      }

    };
  };
};

