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
import gov.nasa.jpf.constraints.api.Expression
import solverComposition.entity.SequentialBehaviour
import solverComposition.entity.SequentialComposition
import solverComposition.entity.SolverWithBehaviour

class SequentialCompositionBuilder : CompositionBuilder<SequentialSolverBuilder, SeqDslSolverBuilder>() {
	private val solvers = mutableListOf<SolverWithBehaviour<SequentialBehaviour>>()
	private lateinit var startWith: (assertions: List<Expression<Boolean>>) -> String

	override fun build(): ConstraintSolver {
		val actualSolvers = solvers.toList()
		solvers.clear()
		return SequentialComposition(actualSolvers, startWith)
	}

	/**
	 * Specifies witch of the integrated SMT-Solvers should be executed first.
	 *
	 * @param func the function that identifies one of the integrated SMT-Solvers by its [SolverBuilder.identifier].
	 */
	fun startWith(func: (assertions: List<Expression<Boolean>>) -> String) {
		startWith = func
	}

	override fun solver(
		idInFactory: String,
		func: SequentialSolverBuilder.() -> Unit
	): String {
		val solverWithBehaviour = SequentialSolverBuilder().apply(func).build(idInFactory)
		this.solvers.add(solverWithBehaviour)
		return solverWithBehaviour.behaviour.identifier
	}

	override fun dslSolver(
		func: SeqDslSolverBuilder.() -> Unit
	): String {
		val solverWithBehaviour = SeqDslSolverBuilder().apply(func).build()
		this.solvers.add(solverWithBehaviour)
		return solverWithBehaviour.behaviour.identifier
	}
}