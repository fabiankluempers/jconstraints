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

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.SolverCompositionDSL
import solverComposition.entity.DSLResult
import java.util.*

class ParallelTestSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("partest")

	override fun createSolver(config: Properties): ConstraintSolver =
		SolverCompositionDSL.parallelComposition {
			solver("mock") {
				identifier = "3000"
				configuration.setProperty("res", "sat")
				configuration.setProperty("timeout", "3000")
				ignoredSubset = setOf(ConstraintSolver.Result.SAT)
				useContext()
			}
			solver("mock") {
				identifier = "4000"
				configuration.setProperty("res", "sat")
				configuration.setProperty("timeout", "4000")
			}
			solver("mock") {
				identifier = "5000"
				configuration.setProperty("res", "sat")
				configuration.setProperty("timeout", "5000")
			}
			if (config.getProperty("run") == "par") {
				val limit = config.getProperty("lim")
				if (limit == null) {
					parallel()
				} else {
					parallelWithLimit(limit.toInt())
				}
			} else {
				sequential()
			}
			parallelWithLimit(5)
			finalVerdict { results ->
				val modeResult = results
					.values
					.groupingBy { it.result }
					.eachCount()
					.maxByOrNull { it.value }?.key ?: ConstraintSolver.Result.DONT_KNOW
				results.entries.find { it.value.result == modeResult }?.value ?: DSLResult.dontKnow()
			}
		}
}



