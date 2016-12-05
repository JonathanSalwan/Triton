//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <cstdlib>
#include <solverModel.hpp>



namespace triton {
  namespace engines {
    namespace solver {

      SolverModel::SolverModel() {
        this->alias = "";
        this->id    = static_cast<triton::uint32>(-1);
        this->name  = "";
        this->value = 0;
      }


      SolverModel::SolverModel(const triton::engines::symbolic::SymbolicVariable* variable, triton::uint512 value) {
        this->alias = variable->getAlias();
        this->id    = variable->getId();
        this->name  = variable->getName();
        this->value = value;
      }


      SolverModel::SolverModel(const SolverModel& other) {
        this->copy(other);
      }


      void SolverModel::copy(const SolverModel& other) {
        this->alias = other.alias;
        this->id    = other.id;
        this->name  = other.name;
        this->value = other.value;
      }


      SolverModel::~SolverModel() {
      }


      const std::string& SolverModel::getName(void) const {
        return this->name;
      }


      const std::string& SolverModel::getAlias(void) const {
        return this->alias;
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
        /* If an alias has been defined, print it */
        if (!model.getAlias().empty())
          stream << model.getAlias() << " = " << std::hex << model.getValue() << std::dec;

        /* Otherwise, we print the default variable name */
        else
          stream << model.getName() << " = " << std::hex << model.getValue() << std::dec;

        return stream;
      }


      std::ostream& operator<<(std::ostream& stream, const SolverModel* model) {
        stream << *model;
        return stream;
      }

    };
  };
};
