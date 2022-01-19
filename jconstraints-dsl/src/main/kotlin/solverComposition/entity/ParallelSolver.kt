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
import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import java.time.Duration
import kotlin.jvm.Throws

class ParallelComposition(
	solvers: Map<String, SolverWithBehaviour<ParallelBehaviour>>,
	val finalVerdict: (solverResults: Map<String, Result>) -> ConstraintSolver.Result,
	val waitFor: Int,
) : ConstraintSolverComposition<ParallelBehaviour>(solvers) {

	//	override fun solve(f: Expression<Boolean>?, result: Valuation?): ConstraintSolver.Result {
//		requireNotNull(f)
//		//Determine which solvers to run
//		val (activeSolvers, inactiveSolvers) = solvers.partition { it.behaviour.runIf(f) }
//
//		//Actually run solvers //TODO respect waitFor
//		runBlocking {
//			activeSolvers.forEach {
//				launch {
//					lateinit var solverResult: ConstraintSolver.Result
//					val valuation = Valuation()
//					try {
//						withTimeout(timerDuration.toMillis()) {
//							solverResult = it.solver.solve(f, valuation)
//						}
//					} catch (e: TimeoutCancellationException) {
//						solverResult = ConstraintSolver.Result.TIMEOUT
//					}
//					finalVerdictMap[it.behaviour.identifier] = Result.fromResult(solverResult)
//				}
//			}
//		}
//
//		//Document result for inactive solvers
//		inactiveSolvers.forEach {
//			finalVerdictMap[it.behaviour.identifier] = Result.DID_NOT_RUN
//		}
//		val finalResult = finalVerdict(finalVerdictMap.toMap())
//		finalVerdictMap.clear()
//		return finalResult
//	}
	override fun solve(f: Expression<Boolean>?, result: Valuation?): ConstraintSolver.Result {
		return ConstraintSolver.Result.DONT_KNOW
	}
}