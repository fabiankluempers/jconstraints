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
import java.util.*


object SolverCompositionDSL {
	fun sequentialComposition(func: SequentialCompositionBuilder.() -> Unit): ConstraintSolver {
		return SequentialCompositionBuilder().apply(func).build()
	}

	fun parallelComposition(func: ParallelCompositionBuilder.() -> Unit): ConstraintSolver {
		return ParallelCompositionBuilder().apply(func).build()
	}
}

@DslMarker
annotation class SolverCompositionDslMarker

@SolverCompositionDslMarker
abstract class CompositionBuilder<T : SolverBuilder<*>, R : SolverBuilder<*>> {
	internal abstract fun build() : ConstraintSolver

	abstract fun dslSolver(func: R.() -> Unit = {}) : String

	abstract fun solver(
		idInFactory: String,
		func: T.() -> Unit = {}
	) : String
}

@SolverCompositionDslMarker
abstract class  SolverBuilder <T : ConstraintSolverBehaviour> {
	val configuration: Properties = Properties()
	lateinit var identifier: String
	protected var runIf: (assertions: List<Expression<Boolean>>) -> Boolean = { true }

	internal abstract fun build(provIdentifier: String? = null) : SolverWithBehaviour<T>

	fun runIf(func: (List<Expression<Boolean>>) -> Boolean) {
		runIf = func
	}
}


