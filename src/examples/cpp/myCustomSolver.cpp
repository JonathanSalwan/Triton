

#include <string>                        // for string

#include <triton/astContext.hpp>         // for AstContext
#include <triton/exceptions.hpp>         // for SolverEngine

#include "MyCustomSolver.h"

namespace triton {
	namespace engines {
		namespace solver {

			MyCustomSolver::MyCustomSolver(triton::engines::symbolic::SymbolicEngine* symbolicEngine) {
				if (symbolicEngine == nullptr)
					throw triton::exceptions::SolverEngine("Z3Solver::Z3Solver(): The symbolicEngine API cannot be null.");
				this->symbolicEngine = symbolicEngine;
			}


			MyCustomSolver::MyCustomSolver(const MyCustomSolver& other) {
				this->symbolicEngine = other.symbolicEngine;
			}


			MyCustomSolver& MyCustomSolver::operator=(const MyCustomSolver& other) {
				this->symbolicEngine = other.symbolicEngine;
				return *this;
			}


			std::list<std::map<triton::uint32, SolverModel>> MyCustomSolver::getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const {
				std::list<std::map<triton::uint32, SolverModel>> ret;
				// Place your code here to solve the formulas
				return ret;
			}


			std::map<triton::uint32, SolverModel> MyCustomSolver::getModel(const triton::ast::SharedAbstractNode& node) const {
				std::map<triton::uint32, SolverModel> ret;
				ret[0] = SolverModel("solver_Name", 0x31337);
				return ret;
			}


			std::string MyCustomSolver::getName(void) const {
				return "MyCustomSolver";
			}

		};
	};
};