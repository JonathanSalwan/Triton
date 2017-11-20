//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <tritonast/solvers/model.hpp>


namespace triton {
  namespace ast {
    namespace solvers {

      Model::Model() {
        this->name  = "";
        this->value = 0;
      }


      Model::Model(const std::string& name, triton::uint512 value) {
        this->name  = name;
        this->value = value;
      }


      Model::Model(const Model& other) {
        this->copy(other);
      }


      void Model::copy(const Model& other) {
        this->name  = other.name;
        this->value = other.value;
      }


      const std::string& Model::getName(void) const {
        return this->name;
      }


      triton::uint512 Model::getValue(void) const {
        return this->value;
      }


      void Model::operator=(const Model& other) {
        this->copy(other);
      }


      std::ostream& operator<<(std::ostream& stream, const Model& model) {
        stream << model.getName() << " = 0x" << std::hex << model.getValue() << std::dec;
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const Model* model) {
        stream << *model;
        return stream;
      }

    }
  };
};
