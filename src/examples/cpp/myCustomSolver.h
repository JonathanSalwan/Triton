//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#pragma once

#include <list>
#include <map>
#include <string>

#include <triton/ast.hpp>
#include <triton/dllexport.hpp>
#include <triton/solverInterface.hpp>
#include <triton/solverModel.hpp>
#include <triton/symbolicEngine.hpp>
#include <triton/tritonTypes.hpp>



//! The Triton namespace
namespace triton {
	/*!
	*  \addtogroup triton
	*  @{
	*/
	//! The Engines namespace
	namespace engines {
		/*!
		*  \ingroup triton
		*  \addtogroup engines
		*  @{
		*/
		//! The Solver namespace
		namespace solver {
			/*!
			*  \ingroup engines
			*  \addtogroup solver
			*  @{
			*/

			//! \class Z3Solver
			/*! \brief Solver engine using z3. */
			class MyCustomSolver : public SolverInterface {
			private:
				//! Symbolic Engine API
				triton::engines::symbolic::SymbolicEngine* symbolicEngine;

			public:
				//! Constructor.
				TRITON_EXPORT MyCustomSolver(triton::engines::symbolic::SymbolicEngine* symbolicEngine);

				//! Constructor by copy.
				TRITON_EXPORT MyCustomSolver(const MyCustomSolver& other);

				//! Operator.
				TRITON_EXPORT MyCustomSolver& operator=(const MyCustomSolver& other);

				//! Computes and returns a model from a symbolic constraint.
				/*! \brief map of symbolic variable id -> model
				*
				* \details
				* **item1**: symbolic variable id<br>
				* **item2**: model
				*/
				TRITON_EXPORT std::map<triton::uint32, SolverModel> getModel(const triton::ast::SharedAbstractNode& node) const;

				//! Computes and returns several models from a symbolic constraint. The `limit` is the number of models returned.
				/*! \brief list of map of symbolic variable id -> model
				*
				* \details
				* **item1**: symbolic variable id<br>
				* **item2**: model
				*/
				TRITON_EXPORT std::list<std::map<triton::uint32, SolverModel>> getModels(const triton::ast::SharedAbstractNode& node, triton::uint32 limit) const;

				//! Returns the name of this solver.
				TRITON_EXPORT std::string getName(void) const;
			};

			/*! @} End of solver namespace */
		};
		/*! @} End of engines namespace */
	};
	/*! @} End of triton namespace */
};

