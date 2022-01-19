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

import com.sun.org.slf4j.internal.LoggerFactory
import gov.nasa.jpf.constraints.api.*
import gov.nasa.jpf.constraints.expressions.LogicalOperator
import gov.nasa.jpf.constraints.expressions.Negation
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression
import gov.nasa.jpf.constraints.expressions.PropositionalCompound
import gov.nasa.jpf.constraints.util.ExpressionUtil
import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import solverComposition.dsl.*
import java.lang.Error
import kotlin.jvm.Throws

class SequentialComposition(
	solvers: Map<String, SolverWithBehaviour<SequentialBehaviour>>,
	val startWith: (assertions: List<Expression<Boolean>>) -> String
) : ConstraintSolverComposition<SequentialBehaviour>(solvers) {

	//	override fun solve(f: Expression<Boolean>?, result: Valuation?): ConstraintSolver.Result {
//		requireNotNull(f)
//		var isContinue: Boolean = true
//		var solverIndex: Int = 0
//		while (isContinue) {
//			val (solver, behaviour) = solvers[solverIndex]
//			//determine if solver should be executed
//			if (behaviour.runIf(f)) {
//				val valuation = Valuation()
//				lateinit var solverResult: ConstraintSolver.Result
//				//execute solver with timeout
//				runBlocking {
//					try {
//						withTimeout(behaviour.timerDuration.toMillis()) {
//							solverResult = solver.solve(f, valuation)
//						}
//					} catch (e: TimeoutCancellationException) {
//						solverResult = ConstraintSolver.Result.TIMEOUT
//					}
//				}
//				//write result
//				finalVerdictMap[behaviour.identifier] = Result.fromResult(solverResult)
//				isContinue = behaviour.continueIf(f, Result.fromResult(solverResult), valuation)
//			} else {
//				finalVerdictMap[behaviour.identifier] = Result.DID_NOT_RUN
//			}
//			solverIndex++
//		}
//		//write result for remaining solvers, that won't get executed
//		for (i in solverIndex until solvers.size) {
//			finalVerdictMap[solvers[i].behaviour.identifier] = Result.DID_NOT_RUN
//		}
//		//calculate finalVerdict
//		val finalResult = finalVerdict(finalVerdictMap.toMap())
//		finalVerdictMap.clear()
//		return finalResult
//	}
	override fun solve(f: Expression<Boolean>?, result: Valuation?): ConstraintSolver.Result {
		return ConstraintSolver.Result.DONT_KNOW
	}

	override fun dslSolve(assertions: MutableList<Expression<Boolean>>?): DSLResult {
		var actualAssertions = assertions?.toList() ?: listOf()
		var currentSolver = solvers[startWith(assertions?.toList() ?: listOf())]
		checkNotNull(currentSolver) { "startWith returned a solver identifier that is not valid in this composition" }
		while (true) {
			var isUnsatCore = false
			checkNotNull(currentSolver) { "continuation returned a solver identifier that is not valid in this composition" }
			val behaviour = currentSolver.behaviour
			println("starting solver ${currentSolver.behaviour.identifier}")
			var dslResult = Result.DID_NOT_RUN
			lateinit var actualResult: ConstraintSolver.Result
			var valuation = Valuation()
			if (behaviour.useContext) {
				val ctx: SolverContext = try {
					currentSolver.solver.createContext()
				} catch (e: UnsupportedOperationException) {
					println("The solver ${currentSolver.behaviour.identifier} does not support context. Stopping with ERROR")
					return DSLResult(ConstraintSolver.Result.ERROR, Valuation())
				}

				if (behaviour.enableUnsatCore) {
					if (ctx is UNSATCoreSolver) {
						ctx.enableUnsatTracking()
						isUnsatCore = true
					} else {
						println("The solver ${currentSolver.behaviour.identifier} does not support unsat core feature. Stopping with ERROR")
						return DSLResult(ConstraintSolver.Result.ERROR, Valuation())
					}
				}
				if (behaviour.runIf(actualAssertions)) {
					ctx.add(actualAssertions)
					actualResult = ctx.solve(valuation)
					dslResult = Result.fromResult(actualResult)
				}
				val continuation = determineContinuation(behaviour.continuation, dslResult, actualAssertions, valuation)
				when (continuation.continueMode) {
					is Continue -> {
						if (continuation.replaceWithCore) {
							if (isUnsatCore) {
								actualAssertions = (ctx as UNSATCoreSolver).unsatCore
								//TODO check if empty?
							} else {
								println("Continuation of the solver ${currentSolver.behaviour.identifier} tried to replace wit unsat core but solver does not support it. Continuing with original assertions")
							}
						}
						if (continuation.replaceWithNewModel) {
							//TODO new model
						}
						currentSolver = solvers[continuation.continueMode.identifer]
					}
					is Stop -> {
						return DSLResult(actualResult, valuation)
					}
				}
			} else {
				val solver = currentSolver.solver
				if (behaviour.enableUnsatCore) {
					if (solver is UNSATCoreSolver) {
						solver.enableUnsatTracking()
						isUnsatCore = true
					} else {
						println("The solver ${currentSolver.behaviour.identifier} does not support unsat core feature. Stopping with ERROR")
						return DSLResult(ConstraintSolver.Result.ERROR, Valuation())
					}
				}
				if (behaviour.runIf(actualAssertions)) {
					val dslSolveResult: DSLResult = try {
						solver.dslSolve(actualAssertions)
					} catch (e: UnsupportedOperationException) {
						println("The solver ${currentSolver.behaviour.identifier} does not support dslSolve. Falling back to solve")
						DSLResult(solver.solve(ExpressionUtil.and(actualAssertions), valuation), valuation)
					}
					actualResult = dslSolveResult.result
					dslResult = Result.fromResult(dslSolveResult.result)
					valuation = dslSolveResult.valuation
				}
				val continuation = determineContinuation(behaviour.continuation, dslResult, actualAssertions, valuation)
				when (continuation.continueMode) {
					is Continue -> {
						if (continuation.replaceWithCore) {
							if (isUnsatCore) {
								actualAssertions = (solver as UNSATCoreSolver).unsatCore
								//TODO check if empty?
							} else {
								println("Continuation of the solver ${currentSolver.behaviour.identifier} tried to replace wit unsat core but solver does not support it. Continuing with original assertions")
							}
						}
						if (continuation.replaceWithNewModel) {
							//TODO new model
						}
						currentSolver = solvers[continuation.continueMode.identifer]
					}
					is Stop -> {
						return DSLResult(actualResult, valuation)
					}
				}
			}
		}
	}

	private fun determineContinuation(
		continuation: ((List<Expression<Boolean>>, ContinuationResult, Valuation) -> ContinuationBuilder),
		res: Result,
		assertions: List<Expression<Boolean>>,
		valuation: Valuation
	) = when (res) {
		Result.SAT -> continuation(assertions, Sat, valuation)
		Result.UNSAT -> continuation(assertions, Unsat, valuation)
		Result.DONT_KNOW -> continuation(assertions, DontKnow, valuation)
		Result.ERROR -> continuation(assertions, Error, valuation)
		Result.TIMEOUT -> continuation(assertions, Timeout, valuation)
		Result.DID_NOT_RUN -> continuation(assertions, DidNotRun, valuation)
	}.continuation

}
