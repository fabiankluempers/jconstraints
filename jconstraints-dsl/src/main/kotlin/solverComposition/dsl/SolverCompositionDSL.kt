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
import solverComposition.entity.*


object SolverCompositionDSL {
	fun sequentialComposition(func: SequentialCompositionBuilder.() -> Unit): ConstraintSolver {
		return SequentialCompositionBuilder().apply(func).build()
	}

	fun parallelComposition(func: ParallelCompositionBuilder.() -> Unit): ConstraintSolver {
		return ParallelCompositionBuilder().apply(func).build()
	}

}

abstract class CompositionBuilder<T : SolverBuilder<*>> {
	protected lateinit var finalVerdict : (Map<String, ConstraintSolverComposition.Result>) -> ConstraintSolver.Result
	internal abstract fun build() : ConstraintSolver
	fun finalVerdict(func: (solverResults: Map<String, ConstraintSolverComposition.Result>) -> ConstraintSolver.Result) {
		finalVerdict = func
	}

	abstract fun solver(
		solver: ConstraintSolver,
		func: T.() -> Unit = {}
	)
}

abstract class  SolverBuilder <T: ConstraintSolverBehaviour>{
	lateinit var identifier: String
	protected val featureFlags: Map<String, Boolean> = mutableMapOf()
	protected lateinit var runIf: (Expression<Boolean>) -> Boolean

	internal abstract fun build() : T

	fun runIf(func: (expression: Expression<Boolean>) -> Boolean) {
		runIf = func
	}
}

