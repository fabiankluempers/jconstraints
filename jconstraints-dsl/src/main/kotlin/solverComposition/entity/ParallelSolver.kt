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
import java.util.concurrent.Callable
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import kotlin.math.min

class ParallelComposition(
	solvers: Map<String, SolverWithBehaviour<ParallelBehaviour>>,
	val finalVerdict: (solverResults: Map<String, DSLResult>) -> DSLResult,
	val waitFor: Int,
) : ConstraintSolverComposition<ParallelBehaviour>(solvers) {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): ConstraintSolver.Result {
		return ConstraintSolver.Result.DONT_KNOW
	}

	override fun dslSolve(assertions: MutableList<Expression<Boolean>>?): DSLResult {
		val actualAssertions = assertions?.toList() ?: listOf()
		val activeSolvers = solvers.values.filter { it.behaviour.runIf(actualAssertions) }
		val latch = CountDownLatch(min(activeSolvers.size, waitFor))
		val workers = activeSolvers.map { Worker(it, actualAssertions, latch) }
		val exec = Executors.newFixedThreadPool(activeSolvers.size)
		val results = workers.map { exec.submit(it) }
		val resultMap = mutableMapOf<String, DSLResult>()
		latch.await()
		results.forEach {
			if (it.isDone) {
				val result = it.get()
				resultMap[result.first] = result.second
			} else {
				it.cancel(true)
			}
		}
		exec.shutdown()
		return finalVerdict(resultMap.toMap())
	}

	inner class Worker(
		private val solver: SolverWithBehaviour<ParallelBehaviour>,
		private val assertions: List<Expression<Boolean>>,
		private val latch: CountDownLatch
	) : Callable<Pair<String, DSLResult>> {
		override fun call(): Pair<String, DSLResult> {
			println("Starting solver ${solver.behaviour.identifier}")
			val behaviour = solver.behaviour
			if (behaviour.useContext) {
				val ctx: SolverContext = try {
					solver.solver.createContext()
				} catch (e: UnsupportedOperationException) {
					println("The solver ${solver.behaviour.identifier} does not support context. Stopping with ERROR")
					return solver.behaviour.identifier to DSLResult(
						Result.ERROR,
						Valuation()
					).also { latch.countDown() }
				}
				ctx.add(assertions)
				val valuation = Valuation()
				return solver.behaviour.identifier to DSLResult(
					ctx.solve(valuation),
					valuation
				).also { latch.countDown() }
			} else {
				val result : DSLResult = try {
					solver.solver.dslSolve(assertions)
				} catch (e : UnsupportedOperationException) {
					println("The solver ${solver.behaviour.identifier} does not support dslSolve. Falling back to solve")
					val valuation = Valuation()
					return solver.behaviour.identifier to DSLResult(
						solver.solver.solve(ExpressionUtil.and(assertions), valuation),
						valuation
					).also { latch.countDown() }
				}
				return (solver.behaviour.identifier to result).also { latch.countDown() }
			}
		}

	}
}
