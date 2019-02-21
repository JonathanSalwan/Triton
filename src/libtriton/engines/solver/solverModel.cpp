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
        this->value = 0;
      }


      SolverModel::SolverModel(const triton::engines::symbolic::SharedSymbolicVariable& variable, triton::uint512 value) {
        this->value    = value;
        this->variable = variable;
      }


      SolverModel::SolverModel(const SolverModel& other) {
        this->copy(other);
      }


      void SolverModel::copy(const SolverModel& other) {
        this->value    = other.value;
        this->variable = other.variable;
      }


      triton::usize SolverModel::getId(void) const {
        return this->variable->getId();
      }


      triton::uint512 SolverModel::getValue(void) const {
        return this->value;
      }


      const triton::engines::symbolic::SharedSymbolicVariable& SolverModel::getVariable(void) const {
        return this->variable;
      }


      SolverModel& SolverModel::operator=(const SolverModel& other) {
        this->copy(other);
        return *this;
      }


      std::ostream& operator<<(std::ostream& stream, const SolverModel& model) {
        stream << model.getVariable() << " = 0x" << std::hex << model.getValue() << std::dec;
        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const SolverModel* model) {
        stream << *model;
        return stream;
      }

    };
  };
};
