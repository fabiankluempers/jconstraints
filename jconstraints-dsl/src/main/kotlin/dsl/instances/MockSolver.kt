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
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import java.util.*

class MockSolver(private val res: Result, private val runtime: Long) : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		try {
			Thread.sleep(runtime)
		} catch (e: InterruptedException) {
			//println("mock solver was interrupted")
			return res
		}
		//println("mock solver was not interrupted")
		return res
	}
}

class MockSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("Mock", "mock")

	override fun createSolver(config: Properties): ConstraintSolver {
		val actualResult = when (config.getProperty("res", "unknown")) {
			"sat" -> ConstraintSolver.Result.SAT
			"unsat" -> ConstraintSolver.Result.UNSAT
			"unknown" -> ConstraintSolver.Result.DONT_KNOW
			"error" -> ConstraintSolver.Result.ERROR
			"timeout" -> ConstraintSolver.Result.TIMEOUT
			else -> ConstraintSolver.Result.UNSAT
		}
		return MockSolver(actualResult, config.getProperty("timeout", "0").toLong())
	}
}