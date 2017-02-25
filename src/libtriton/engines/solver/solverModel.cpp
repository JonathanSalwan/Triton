//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdlib>

#include <triton/solverModel.hpp>
#include <triton/symbolicEnums.hpp>



namespace triton {
  namespace engines {
    namespace solver {

      SolverModel::SolverModel() {
        this->id    = static_cast<triton::uint32>(-1);
        this->name  = "";
        this->value = 0;
      }


      SolverModel::SolverModel(const std::string& name, triton::uint512 value) {
        this->id    = std::atoi(name.c_str() + TRITON_SYMVAR_NAME_SIZE);
        this->name  = name;
        this->value = value;
      }


      SolverModel::SolverModel(const SolverModel& other) {
        this->copy(other);
      }


      void SolverModel::copy(const SolverModel& other) {
        this->id    = other.id;
        this->name  = other.name;
        this->value = other.value;
      }


      SolverModel::~SolverModel() {
      }


      const std::string& SolverModel::getName(void) const {
        return this->name;
      }


      triton::uint32 SolverModel::getId(void) const {
        return this->id;
      }


      triton::uint512 SolverModel::getValue(void) const {
        return this->value;
      }


      void SolverModel::operator=(const SolverModel& other) {
        this->copy(other);
      }


      std::ostream& operator<<(std::ostream& stream, const SolverModel& model) {
        stream << model.getName() << " = 0x" << std::hex << model.getValue() << std::dec;
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const SolverModel* model) {
        stream << *model;
        return stream;
      }

    };
  };
};
