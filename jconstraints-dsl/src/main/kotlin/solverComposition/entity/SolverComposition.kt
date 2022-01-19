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

	enum class Result {
		SAT,
		UNSAT,
		DONT_KNOW,
		ERROR,
		TIMEOUT,
		DID_NOT_RUN;

		fun ran() = this != DID_NOT_RUN

		fun toResult() = when (this) {
			SAT -> ConstraintSolver.Result.SAT
			UNSAT -> ConstraintSolver.Result.UNSAT
			DONT_KNOW -> ConstraintSolver.Result.DONT_KNOW
			ERROR -> ConstraintSolver.Result.ERROR
			TIMEOUT -> ConstraintSolver.Result.TIMEOUT
			DID_NOT_RUN -> throw ClassCastException("Can not convert DID_NOT_RUN constant to a ${ConstraintSolver.Result::class}.")
		}

		companion object {
			fun fromResult(res: ConstraintSolver.Result) = when (res) {
				ConstraintSolver.Result.SAT -> SAT
				ConstraintSolver.Result.UNSAT -> UNSAT
				ConstraintSolver.Result.DONT_KNOW -> DONT_KNOW
				ConstraintSolver.Result.TIMEOUT -> TIMEOUT
				ConstraintSolver.Result.ERROR -> ERROR
			}
		}
	}
}

class DuplicateSolverIdentifierException(message: String) : Exception(message)

data class SolverWithBehaviour<T : ConstraintSolverBehaviour>(val solver: ConstraintSolver, val behaviour: T)
