//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <tritonast/exceptions.hpp>
#include <tritonast/representations/representation.hpp>

#include <new>
#include <memory>


namespace triton {
  namespace ast {
    namespace representations {

      Representation::Representation() {
        /* Set the default representation */
        this->mode = triton::ast::representations::SMT_REPRESENTATION;

        /* Init representations interface */
        this->representations[triton::ast::representations::SMT_REPRESENTATION] = std::unique_ptr<triton::ast::representations::Smt>(new(std::nothrow) triton::ast::representations::Smt());
        this->representations[triton::ast::representations::PYTHON_REPRESENTATION] = std::unique_ptr<triton::ast::representations::Python>(new(std::nothrow) triton::ast::representations::Python());

        if (this->representations[triton::ast::representations::SMT_REPRESENTATION] == nullptr)
          throw triton::ast::exceptions::Representation("Representation::Representation(): Cannot allocate a new representation instance.");

        if (this->representations[triton::ast::representations::PYTHON_REPRESENTATION] == nullptr)
          throw triton::ast::exceptions::Representation("Representation::Representation(): Cannot allocate a new representation instance.");
      }


      triton::uint32 Representation::getMode(void) const {
        return this->mode;
      }


      void Representation::setMode(triton::uint32 mode) {
        if (mode >= triton::ast::representations::LAST_REPRESENTATION)
          throw triton::ast::exceptions::Representation("Representation::setMode(): Invalid representation mode.");
        this->mode = mode;
      }


      std::ostream& Representation::print(std::ostream& stream, AbstractNode* node) {
        return this->representations[this->mode]->print(stream, node);
      }

    };
  };
};

