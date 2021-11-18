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
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeout
import kotlin.jvm.Throws

class SequentialComposition(
	solvers: List<SolverWithBehaviour<SequentialBehaviour>>,
	finalVerdict: (solverResults: Map<String, Result>) -> ConstraintSolver.Result,
) : ConstraintSolverComposition<SequentialBehaviour>(solvers, finalVerdict) {

	override fun solve(f: Expression<Boolean>?, result: Valuation?): ConstraintSolver.Result {
		requireNotNull(f)
		var isContinue: Boolean = true
		var solverIndex: Int = 0
		while (isContinue) {
			val (solver, behaviour) = solvers[solverIndex]
			if (behaviour.runIf(f)) {
				val valuation = Valuation()
				lateinit var solverResult: ConstraintSolver.Result
				runBlocking {
					try {
						withTimeout(behaviour.timerDuration.toMillis()) {
							solverResult = solver.solve(f, valuation)
						}
					} catch (e: TimeoutCancellationException) {
						solverResult = ConstraintSolver.Result.TIMEOUT
					}
				}
				finalVerdictMap[behaviour.identifier] = Result.fromResult(solverResult)
				isContinue = behaviour.continueIf(f, Result.fromResult(solverResult), valuation)
			} else {
				finalVerdictMap[behaviour.identifier] = Result.DID_NOT_RUN
			}
			solverIndex++
		}
		for (i in solverIndex..solvers.size) {
			finalVerdictMap[solvers[i].behaviour.identifier] = Result.DID_NOT_RUN
		}
		val finalResult = finalVerdict(finalVerdictMap.toMap())
		finalVerdictMap.clear()
		return finalResult
	}

}
