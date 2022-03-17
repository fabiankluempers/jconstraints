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
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import solverComposition.entity.ConstraintSolverBehaviour
import solverComposition.entity.SolverWithBehaviour
import java.util.*


@SolverCompositionDslMarker
abstract class SolverBuilder<T : ConstraintSolverBehaviour> {
	/**
	 * Exposes a [Properties] object that is passed to the [ConstraintSolverFactory] when instantiating this SMT-Solver.
	 */
	val configuration: Properties = Properties()

	/**
	 * The unique identifier of this SMT-Solver in this SolverComposition.
	 *
	 * @see [ParallelCompositionBuilder.finalVerdict]
	 * @see [SequentialCompositionBuilder.startWith]
	 * @see [SequentialSolverBuilder.continuation]
	 */
	lateinit var identifier: String
	protected var runIf: (assertions: List<Expression<Boolean>>) -> Boolean = { true }

	internal abstract fun build(provIdentifier: String? = null): SolverWithBehaviour<T>

	/**
	 * Specifies if this SMT-Solver should be executed in this SolverComposition,
	 * based on the SMT-Problem characterized by the expressions.
	 *
	 * @param func the fucntion that determines whether this SMT-Solver should be executed in this SolverComposition,
	 * based on the expressions
	 */
	fun runIf(func: (List<Expression<Boolean>>) -> Boolean) {
		runIf = func
	}
}