/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package solverComposition.dsl

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import solverComposition.entity.ParallelBehaviour
import solverComposition.entity.SolverWithBehaviour

open class ParallelSolverBuilder : SolverBuilder<ParallelBehaviour>() {

	protected var useContext = false

	/**
	 * Specifies that a Context of this SMT-Solver should be used for solving inside this SolverComposition.
	 */
	fun useContext() {
		useContext = true
	}

	/**
	 * Specifies the ignored subset of possible results for this SMT-Solver.
	 * If an obtained result is in the ignored subset it wont be available in the results map for [ParallelCompositionBuilder.finalVerdict]
	 * and it wont contribute to reaching the limit when [ParallelCompositionBuilder.parallelWithLimit] is set.
	 */
	var ignoredSubset: Set<ConstraintSolver.Result> = setOf()

	override fun build(provIdentifier: String?): SolverWithBehaviour<ParallelBehaviour> {
		return SolverWithBehaviour(
			ConstraintSolverFactory.createSolver(provIdentifier, configuration), ParallelBehaviour(
				identifier = identifier,
				runIf = runIf,
				useContext = useContext,
				ignoredSubset = ignoredSubset
			)
		)
	}
}