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


import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.expressions.Constant
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import solverComposition.dsl.SolverCompositionDSL
import solverComposition.entity.ConstraintSolverComposition
import java.time.Duration

internal class SequentialTest {

	private val solver = SolverCompositionDSL.sequentialComposition {
		solver(TestSatSolver()) {
			runIf { true }
			continueIf { expression, solverRunResult, valuation ->
				when (solverRunResult) {
					ConstraintSolverComposition.Result.SAT -> true
					else -> false
				}
			}
			identifier = "TestSatSolver"
			timerDuration = Duration.ofMillis(2000)
		}
		solver(TestUnsatSolver()) {
			runIf { true }
			continueIf { expression, solverRunResult, valuation ->
				when (solverRunResult) {
					ConstraintSolverComposition.Result.SAT -> true
					else -> false
				}
			}
			identifier = "TestUnsatSolver"
			timerDuration = Duration.ofMillis(2000)
		}
		solver(TestUnsatSolver()) {
			runIf { true }
			continueIf { expression, solverRunResult, valuation ->
				when (solverRunResult) {
					ConstraintSolverComposition.Result.SAT -> true
					else -> false
				}
			}
			identifier = "TestUnsatSolver2"
			timerDuration = Duration.ofMillis(2000)
		}
		finalVerdict {
			it["TestUnsatSolver"]?.toResult() ?: ConstraintSolver.Result.DONT_KNOW
		}
	}

	@Test
	fun testSolver() {
		assertEquals(solver.solve(SMTProblem().allAssertionsAsConjunction, Valuation()), ConstraintSolver.Result.UNSAT)

	}
}