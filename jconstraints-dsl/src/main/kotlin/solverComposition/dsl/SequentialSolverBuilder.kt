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

import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import solverComposition.entity.SequentialBehaviour
import solverComposition.entity.SolverWithBehaviour

open class SequentialSolverBuilder : SolverBuilder<SequentialBehaviour>() {
	protected lateinit var continuation: (assertions: List<Expression<Boolean>>, result: ContinuationResult, valuation: Valuation) -> ContinuationBuilder
	protected var useContext = false
	protected var enableUnsatCoreTracking = false

	/**
	 * Specifies based on the obtained verdict and valuation,
	 * if this SolverComposition should be stopped or continued after this SMT-Solver supplied a verdict.
	 *
	 * @param func the function that determines the Continuation based on assertions, result and valuation.
	 *
	 * @see [ContinuationBuilder]
	 */
	fun continuation(func: (assertions: List<Expression<Boolean>>, result: ContinuationResult, valuation: Valuation) -> ContinuationBuilder) {
		continuation = func
	}

	/**
	 * Specifies that a Context of this SMT-Solver should be used for solving inside this SolverComposition.
	 */
	fun useContext() {
		useContext = true
	}

	/**
	 * Specifies that this SMT-Solver should produce unsatisfiable cores when solving inside this SolverComposition.
	 */
	fun enableUnsatCoreTracking() {
		enableUnsatCoreTracking = true
	}

	override fun build(provIdentifier: String?): SolverWithBehaviour<SequentialBehaviour> {
		return SolverWithBehaviour(
			ConstraintSolverFactory.createSolver(provIdentifier, configuration),
			SequentialBehaviour(
				identifier = identifier,
				runIf = runIf,
				continuation = continuation,
				useContext = useContext,
				enableUnsatCore = enableUnsatCoreTracking,
			)
		)
	}
}