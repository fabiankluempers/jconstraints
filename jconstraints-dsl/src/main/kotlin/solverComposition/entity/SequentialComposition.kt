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

import gov.nasa.jpf.constraints.api.*
import gov.nasa.jpf.constraints.util.ExpressionUtil
import solverComposition.dsl.*
import java.util.logging.Level


class SequentialComposition(
	solvers: List<SolverWithBehaviour<SequentialBehaviour>>,
	private val startWith: (assertions: List<Expression<Boolean>>) -> String
) : ConstraintSolverComposition<SequentialBehaviour>(solvers) {

	override fun createContext(): SolverContext = CompositionContext(this)

	override fun dslSolve(assertions: List<Expression<Boolean>>): DSLResult {
		var actualAssertions = assertions
		var currentSolver = solvers[startWith(actualAssertions)]
		checkNotNull(currentSolver) { "startWith in $this returned a solver identifier that is not valid in this composition" }
		while (true) {
			var isUnsatCore = false
			checkNotNull(currentSolver) { "continuation in $this returned a solver identifier that is not valid in this composition" }
			val behaviour = currentSolver.behaviour
			var continuationResult: ContinuationResult = DidNotRun
			lateinit var actualResult: Result
			var valuation = Valuation()
			if (behaviour.useContext) {
				val ctx: SolverContext = currentSolver.solver.createContext()
				if (behaviour.enableUnsatCore) {
					if (ctx is UNSATCoreSolver) {
						ctx.enableUnsatTracking()
						isUnsatCore = true
					} else {
						logger.log(
							Level.WARNING,
							"The solver with the identifier ${behaviour.identifier} in $this does not support unsat core tracking. Stopping with ERROR"
						)
						return DSLResult(Result.ERROR, Valuation())
					}
				}
				if (behaviour.runIf(actualAssertions)) {
					ctx.add(actualAssertions)
					actualResult = ctx.solve(valuation)
					continuationResult = actualResult.toDslResult()
				}
				val continuation = behaviour.continuation(actualAssertions, continuationResult, valuation).continuation
				when (continuation.continueMode) {
					is Continue -> {
						if (continuation.replaceWithCore) {
							if (isUnsatCore) {
								actualAssertions = (ctx as UNSATCoreSolver).unsatCore
								//TODO check if empty?
							} else {
								logger.log(
									Level.WARNING,
									"Continuation of the solver with the identifier ${behaviour.identifier} in $this tried to replace with unsat core but solver is not enabled for unsat core tracking or does not support it. Continuing with original assertions"
								)
							}
						}
						if (continuation.replaceWithNewModel) {
							//TODO new model
						}
						currentSolver = solvers[continuation.continueMode.identifier]
					}
					is Stop -> {
						return DSLResult(continuation.result, valuation)
					}
				}
				ctx.dispose()
			} else {
				val solver = currentSolver.solver
				if (behaviour.enableUnsatCore) {
					if (solver is UNSATCoreSolver) {
						logger.log(
							Level.WARNING, """The solver with the identifier ${behaviour.identifier} in 
							$this has unsat core tracking enabled but does not use context. 
							The obtained unsat core is probably the same as the input""".trimMargin()
						)
						solver.enableUnsatTracking()
						isUnsatCore = true
					} else {
						logger.log(
							Level.WARNING, """The solver with the identifier ${behaviour.identifier} in $this 
							does not support unsat core tracking. Stopping with ERROR""".trimIndent()
						)
						return DSLResult(Result.ERROR, Valuation())
					}
				}
				if (behaviour.runIf(actualAssertions)) {
					val dslSolveResult =
						DSLResult(solver.solve(ExpressionUtil.and(actualAssertions), valuation), valuation)
					actualResult = dslSolveResult.result
					continuationResult = actualResult.toDslResult()
					valuation = dslSolveResult.valuation
				}
				val continuation = behaviour.continuation(actualAssertions, continuationResult, valuation).continuation
				when (continuation.continueMode) {
					is Continue -> {
						if (continuation.replaceWithCore) {
							if (isUnsatCore) {
								actualAssertions = (solver as UNSATCoreSolver).unsatCore
								//TODO check if empty?
							} else {
								logger.log(
									Level.WARNING, """Continuation of the solver with the identifier 
									${behaviour.identifier} in $this tried to replace with unsat core but solver is not 
									enabled for unsat core tracking or does not support it. 
									Continuing with original assertions""".trimIndent()
								)
							}
						}
						if (continuation.replaceWithNewModel) {
							//TODO new model
						}
						currentSolver = solvers[continuation.continueMode.identifier]
					}
					is Stop -> {
						return DSLResult(continuation.result, valuation)
					}
				}
			}
		}
	}

	private fun Result.toDslResult() =
		when (this) {
			Result.SAT -> Sat
			Result.UNSAT -> Unsat
			Result.DONT_KNOW -> DontKnow
			Result.TIMEOUT -> Timeout
			Result.ERROR -> Error
		}
}
