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
import gov.nasa.jpf.constraints.api.Valuation
import solverComposition.entity.ConstraintSolverComposition
import solverComposition.entity.SequentialBehaviour
import solverComposition.entity.SequentialComposition
import solverComposition.entity.SolverWithBehaviour
import java.time.Duration

class SequentialCompositionBuilder : CompositionBuilder<SequentialSolverBuilder>() {
	private val solvers = mutableListOf<SolverWithBehaviour<SequentialBehaviour>>()
	override fun build(): ConstraintSolver {
		return SequentialComposition(solvers, finalVerdict)
	}

	override fun solver(solver: ConstraintSolver, func: SequentialSolverBuilder.() -> Unit) {
		solvers.add(SolverWithBehaviour(solver, SequentialSolverBuilder().apply(func).build()))
	}
}

class SequentialSolverBuilder : SolverBuilder<SequentialBehaviour>() {
	lateinit var timerDuration: Duration
	private lateinit var continueIf : (Expression<Boolean>, ConstraintSolverComposition.Result, Valuation) -> Boolean

	fun continueIf(func: (Expression<Boolean>, ConstraintSolverComposition.Result, Valuation) -> Boolean) {
		continueIf = func
	}

	override fun build(): SequentialBehaviour {
		return SequentialBehaviour(
			identifier = identifier,
			featureFlags = featureFlags,
			timerDuration = timerDuration,
			runIf = runIf,
			continueIf = continueIf,
		)
	}
}


//region features


fun SequentialSolverBuilder.enableFeatures(func: FeatureBlock.() -> Unit) {

}

class FeatureBlock {

}

fun FeatureBlock.unsatCoreTracking(): UnsatCoreTrackingFeature {
	return UnsatCoreTrackingFeature()
}

class UnsatCoreTrackingFeature {
	infix fun force(flag: Boolean) {

	}
}


fun FeatureBlock.negatedValuation() {

}
//endregion
