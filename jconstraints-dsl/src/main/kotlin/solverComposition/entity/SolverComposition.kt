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
import gov.nasa.jpf.constraints.api.SolverContext
import gov.nasa.jpf.constraints.api.Valuation
import solverComposition.dsl.ContinuationBuilder
import solverComposition.dsl.ContinuationResult
import java.util.*
import java.util.logging.Level
import java.util.logging.Logger

abstract class ConstraintSolverBehaviour(
	val identifier: String,
	val runIf: (List<Expression<Boolean>>) -> Boolean,
	val useContext: Boolean,
	val config: Properties,
)

class SequentialBehaviour(
	identifier: String,
	runIf: (List<Expression<Boolean>>) -> Boolean,
	val continuation: (List<Expression<Boolean>>, ContinuationResult, Valuation) -> ContinuationBuilder,
	val enableUnsatCore: Boolean,
	useContext: Boolean,
	config: Properties,
) : ConstraintSolverBehaviour(identifier, runIf, useContext, config)

class ParallelBehaviour(
	identifier: String,
	runIf: (List<Expression<Boolean>>) -> Boolean,
	useContext: Boolean,
	config: Properties,
) : ConstraintSolverBehaviour(identifier, runIf, useContext, config)

data class DSLResult(val result: ConstraintSolver.Result, val valuation: Valuation)

abstract class ConstraintSolverComposition<T : ConstraintSolverBehaviour>(
	val solvers: Map<String, SolverWithBehaviour<T>>,
) : ConstraintSolver() {
	protected val logger: Logger = Logger.getLogger("jconstraints dsl")

	init {
		require(
			//TODO fix
//			solvers
//				.groupBy { it.behaviour.identifier }
//				.values
//				.all { it.size == 1 }
			true
		)
	}

	abstract fun dslSolve(assertions: List<Expression<Boolean>>): solverComposition.entity.DSLResult

	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		logger.log(Level.INFO, "The solve method won't produce useful unsat cores in this composition. Use dslSolve if any of the solvers contained in this composition have unsatCoreTracking enabled.")
		val dslResult = dslSolve(listOf(f ?: throw IllegalArgumentException("f should not be null")))
		result?.putAll(dslResult.valuation)
		return dslResult.result
	}
}

class CompositionContext(private val comp: ConstraintSolverComposition<*>) : SolverContext() {
	val assertionStack : MutableList<MutableList<Expression<Boolean>>> = mutableListOf(mutableListOf())

	override fun push() {
		assertionStack.add(mutableListOf())
	}

	override fun pop(n: Int) {
		repeat(n) {
			assertionStack.removeLastOrNull()
		}
		if (assertionStack.isEmpty()) {
			assertionStack.add(mutableListOf())
		}
	}

	override fun solve(`val`: Valuation?): ConstraintSolver.Result {
		with(comp.dslSolve(assertionStack.flatten())) {
			`val`?.putAll(valuation)
			return result
		}
	}

	override fun add(expressions: MutableList<Expression<Boolean>>?) {
		if (expressions != null) {
			assertionStack.last().addAll(expressions)
		}

	}

	override fun dispose() {
		assertionStack.clear()
		assertionStack.add(mutableListOf())
	}
}

class DuplicateSolverIdentifierException(message: String) : Exception(message)

data class SolverWithBehaviour<T : ConstraintSolverBehaviour>(val solver: ConstraintSolver, val behaviour: T)
