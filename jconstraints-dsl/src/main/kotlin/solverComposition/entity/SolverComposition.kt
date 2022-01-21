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

package solverComposition.entity

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import solverComposition.dsl.Continuation
import solverComposition.dsl.ContinuationBuilder
import solverComposition.dsl.ContinuationResult
import java.sql.Time
import java.util.*
import java.util.concurrent.TimeUnit
import java.util.logging.Level
import java.util.logging.Logger
import kotlin.time.Duration
import kotlin.time.DurationUnit

abstract class ConstraintSolverBehaviour(
	val identifier: String,
	val runIf: (List<Expression<Boolean>>) -> Boolean,
	val useContext: Boolean,
	val config: Properties,
)

class SequentialBehaviour(
	identifier: String,
	runIf: (List<Expression<Boolean>>) -> Boolean,
	val continuation: (List<Expression<Boolean>>, ContinuationResult, Valuation) -> ContinuationBuilder,
	val enableUnsatCore: Boolean,
	useContext: Boolean,
	config: Properties,
) : ConstraintSolverBehaviour(identifier, runIf, useContext, config)

class ParallelBehaviour(
	identifier: String,
	runIf: (List<Expression<Boolean>>) -> Boolean,
	useContext: Boolean,
	config: Properties,
) : ConstraintSolverBehaviour(identifier, runIf, useContext, config)

abstract class ConstraintSolverComposition<T : ConstraintSolverBehaviour>(
	val solvers: Map<String, SolverWithBehaviour<T>>,
) : ConstraintSolver() {
	protected val logger: Logger = Logger.getLogger("jconstraints dsl")

	init {
		require(
			//TODO fix
//			solvers
//				.groupBy { it.behaviour.identifier }
//				.values
//				.all { it.size == 1 }
			true
		)
	}

	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		logger.log(Level.INFO, "The solve method won't produce useful unsat cores in this composition. Use dslSolve if any of the solvers contained in this composition have unsatCoreTracking enabled.")
		val dslResult = dslSolve(mutableListOf(f))
		result?.putAll(dslResult.valuation)
		return dslResult.result
	}
}

class DuplicateSolverIdentifierException(message: String) : Exception(message)

data class SolverWithBehaviour<T : ConstraintSolverBehaviour>(val solver: ConstraintSolver, val behaviour: T)
