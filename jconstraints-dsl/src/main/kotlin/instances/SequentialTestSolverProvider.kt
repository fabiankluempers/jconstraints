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

package instances

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.*
import solverComposition.entity.DSLResult
import tools.aqua.jconstraints.solvers.portfolio.sequential.StringOrFloatExpressionVisitor
import java.util.*

class SequentialTestSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> {
		return Array(1) { "seqtest" }
	}

	override fun createSolver(config: Properties?): ConstraintSolver = SolverCompositionDSL.sequentialComposition {
		solver("z3") {
			identifier = "z3"
			runIf {
				println(it)
				true
			}

			enableUnsatCoreTracking()

			useContext()

			continuation { assertions, result, valuation ->
				when (result) {
					is Sat -> if (assertions.all { it.evaluateSMT(valuation) }) result.stop() else result continueWith "dk"
					is Unsat -> result continueWith "dk" andReplaceWith UnsatCore
					is DontKnow -> result continueWith "dk"
					else -> result stopWith Result.DONT_KNOW
				}
			}
		}

		solver("dontKnow") {

			identifier = "dk"

			runIf {
				println(it)
				true
			}

			continuation { _, result, _ ->
				result.stop()
			}
		}

		startWith { assertions ->
			println(assertions)
			"z3"
		}
	}

	fun a() {
		SolverCompositionDSL.parallelComposition {
			solver("seqtest") {
				identifier = "afjlkjdsg"
				useContext()
				runIf {
					true
				}
			}
			finalVerdict { results ->
				results["afjlkjdsg"] ?: DSLResult(ConstraintSolver.Result.DONT_KNOW, Valuation())
			}
		}
	}
}