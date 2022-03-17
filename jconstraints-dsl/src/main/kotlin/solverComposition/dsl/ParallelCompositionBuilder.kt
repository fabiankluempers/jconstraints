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
import solverComposition.entity.*

class ParallelCompositionBuilder : CompositionBuilder<ParallelSolverBuilder, ParDslSolverBuilder>() {
	private val solvers = mutableListOf<SolverWithBehaviour<ParallelBehaviour>>()
	private lateinit var finalVerdict: (Map<String, DSLResult>) -> DSLResult
	override fun build(): ConstraintSolver {
		val actualSolvers = solvers.toList()
		solvers.clear()
		return ParallelComposition(
			solvers = actualSolvers,
			runConf = if (runConfiguration.limit < 0) runConfiguration.copy(limit = actualSolvers.size) else runConfiguration,
			finalVerdict = finalVerdict,
		)
	}

	private lateinit var runConfiguration: RunConf

	/**
	 * Specifies that the integrated SMT-Solvers should be executed sequentially
	 */
	fun sequential() {
		runConfiguration = RunConf(RunConfiguration.SEQUENTIAL, 0)
	}

	/**
	 * Specifies that the integrated SMT-Solvers should be executed in parallel with a limit.
	 * An integrated SMT-Solver only counts towards reaching the limit if the obtained verdict is not in its ignoredSubset.
	 *
	 * @see ParallelSolverBuilder.ignoredSubset
	 *
	 * @param limit the limit
	 */
	fun parallelWithLimit(limit: Int) {
		runConfiguration = RunConf(RunConfiguration.PARALLEL, limit)
	}

	/**
	 * Specifies that the integrated SMT-Solvers should be executed in parallel.
	 */
	fun parallel() {
		runConfiguration = RunConf(RunConfiguration.PARALLEL, -1)
	}

	/**
	 * Specifies how all the obtained verdicts from the integrated SMT-Solvers should be aggregated into a final verdict.
	 *
	 * @param func the aggregation function.
	 * The [DSLResult] of an integrated SMT-Solver is referenced by it [SolverBuilder.identifier] in the results map.
	 */
	fun finalVerdict(func: (results: Map<String, DSLResult>) -> DSLResult) {
		finalVerdict = func
	}

	override fun solver(idInFactory: String, func: ParallelSolverBuilder.() -> Unit): String {
		val solverWithBehaviour = ParallelSolverBuilder().apply(func).build(idInFactory)
		solvers.add(solverWithBehaviour)
		return solverWithBehaviour.behaviour.identifier
	}

	override fun dslSolver(func: ParDslSolverBuilder.() -> Unit): String {
		val solverWithBehaviour = ParDslSolverBuilder().apply(func).build()
		solvers.add(solverWithBehaviour)
		return solverWithBehaviour.behaviour.identifier
	}
}

