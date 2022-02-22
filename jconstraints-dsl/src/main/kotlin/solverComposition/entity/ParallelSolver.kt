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

class ParallelComposition(
	solvers: List<SolverWithBehaviour<ParallelBehaviour>>,
	private val finalVerdict: (solverResults: Map<String, DSLResult>) -> DSLResult,
	private val runConf: RunConf,
) : ConstraintSolverComposition<ParallelBehaviour>(solvers) {

	override fun createContext(): SolverContext = CompositionContext(this)

	private fun seqDslSolve(assertions: List<Expression<Boolean>>): DSLResult {
		val activeSolvers = solvers.values.filter { it.behaviour.runIf(assertions) }
		val resultMap = mutableMapOf<String, DSLResult>()
		for (solverWithBehaviour in activeSolvers) {
			if (solverWithBehaviour.behaviour.useContext) {
				val ctx = solverWithBehaviour.solver.createContext()
				ctx.add(assertions)
				val valuation = Valuation()
				val res = ctx.solve(valuation)
				ctx.dispose()
				if (res !in solverWithBehaviour.behaviour.ignoredSubset)
					resultMap[solverWithBehaviour.behaviour.identifier] = DSLResult(res, valuation)
			} else {
				val valuation = Valuation()
				val res = solverWithBehaviour.solver.solve(ExpressionUtil.and(assertions), valuation)
				if (res !in solverWithBehaviour.behaviour.ignoredSubset)
					resultMap[solverWithBehaviour.behaviour.identifier] = DSLResult(res, valuation)
			}
		}
		return finalVerdict.invoke(resultMap.toMap())
	}

	private fun parDslSolve(assertions: List<Expression<Boolean>>): DSLResult {
		val activeSolvers = solvers.values.filter { it.behaviour.runIf(assertions) }
		val waitForLatch = CountDownLatch(runConf.limit)
		val remainingLatch = CountDownLatch(activeSolvers.size)
		val workers = activeSolvers.map { Worker(it, assertions, remainingLatch, waitForLatch) }
		val exec = Executors.newFixedThreadPool(activeSolvers.size)
		val resultMap = mutableMapOf<String, DSLResult>()
		val waiter = Thread {
			try {
				waitForLatch.await()
			} catch (e: InterruptedException) {
				return@Thread
			}
			while (remainingLatch.count > 0) {
				remainingLatch.countDown()
			}
		}
		waiter.start()
		val results = workers.map { exec.submit(it) }
		remainingLatch.await()
		waiter.interrupt()
		results.forEach {
			if (it.isDone) {
				val result = it.get()
				resultMap[result.first] = result.second
			} else {
				it.cancel(true)
			}
		}
		exec.shutdown()
		return finalVerdict(resultMap.filter { it.value.result !in solvers[it.key]!!.behaviour.ignoredSubset }.toMap())
	}

	inner class Worker(
		private val solver: SolverWithBehaviour<ParallelBehaviour>,
		private val assertions: List<Expression<Boolean>>,
		private val remainingLatch: CountDownLatch,
		private val waitForLatch: CountDownLatch,
	) : Callable<Pair<String, DSLResult>> {
		override fun call(): Pair<String, DSLResult> {
			var waitForCountdown = false
			try {
				val behaviour = solver.behaviour
				if (behaviour.useContext) {
					val ctx = solver.solver.createContext()
					ctx.add(assertions)
					val valuation = Valuation()
					return solver.behaviour.identifier to DSLResult(
						ctx.solve(valuation),
						valuation
					).also {
						ctx.dispose()
						if (it.result !in behaviour.ignoredSubset) waitForCountdown = true
					}
				} else {
					val valuation = Valuation()
					return solver.behaviour.identifier to DSLResult(
						solver.solver.solve(ExpressionUtil.and(assertions), valuation),
						valuation
					).also { if (it.result !in behaviour.ignoredSubset) waitForCountdown = true }
				}
			} finally {
				if (waitForCountdown) {
					waitForLatch.countDown()
				}
				remainingLatch.countDown()
			}
		}
	}

	override fun dslSolve(assertions: List<Expression<Boolean>>): DSLResult = when (runConf.conf) {
		RunConfiguration.PARALLEL -> parDslSolve(assertions)
		RunConfiguration.SEQUENTIAL -> seqDslSolve(assertions)
	}
}

