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

package dsl.instances

import IsMulExpressionVisitor
import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.*
import java.util.*
import kotlin.random.Random


fun List<Expression<Boolean>>.evaluateSMT(valuation: Valuation) = all { it.evaluateSMT(valuation) }

class SequentialTestSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> {
		return Array(1) { "seqtest" }
	}


	override fun createSolver(config: Properties?): ConstraintSolver = SolverCompositionDSL.sequentialComposition {
		solver("a") {
			identifier = "dk"
			runIf {
				println("Dont Know input $it")
				true
			}
			useContext()
			continuation { assertions, result, valuation ->
				when (result) {
					is Sat -> {
						if (assertions.evaluateSMT(valuation)) result stopWith Result.SAT
						else result continueWith "Z3"
					}
					is Unsat -> result continueWith "Z3" andReplaceAssertionsWith UnsatCore
					else -> result continueWith "Z3"
				}
			}
		}

		solver("z3") {
			identifier = "z3"
			runIf {
				println("Z3 input: $it")
				true
			}
			enableUnsatCoreTracking()
			useContext()
			continuation { assertions, result, valuation ->
				when (result) {
					is Sat -> {
						if (assertions.evaluateSMT(valuation))
							result.stop()
						else
							result continueWith "dk"
					}
					is Unsat -> result continueWith "dk" andReplaceAssertionsWith UnsatCore
					else -> result stopWith Result.DONT_KNOW
				}
			}
		}

		startWith { assertions ->
			println("start with input: $assertions")
			"z3"
		}
	}
}

