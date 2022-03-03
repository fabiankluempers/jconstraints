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

package solverComposition.dsl

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import solverComposition.entity.SequentialBehaviour
import solverComposition.entity.SequentialComposition
import solverComposition.entity.SolverWithBehaviour

class SequentialCompositionBuilder : CompositionBuilder<SequentialSolverBuilder, SeqDslSolverBuilder>() {
	private val solvers = mutableListOf<SolverWithBehaviour<SequentialBehaviour>>()
	private lateinit var startWith: (assertions: List<Expression<Boolean>>) -> String

	override fun build(): ConstraintSolver {
		val actualSolvers = solvers.toList()
		solvers.clear()
		return SequentialComposition(actualSolvers, startWith)
	}

	fun startWith(func: (assertions: List<Expression<Boolean>>) -> String) {
		startWith = func
	}

	override fun solver(
		solver: String,
		func: SequentialSolverBuilder.() -> Unit
	): String {
		val solverWithBehaviour = SequentialSolverBuilder().apply(func).build(solver)
		this.solvers.add(solverWithBehaviour)
		return solverWithBehaviour.behaviour.identifier
	}

	override fun dslSolver(
		func: SeqDslSolverBuilder.() -> Unit
	): String {
		val solverWithBehaviour = SeqDslSolverBuilder().apply(func).build()
		this.solvers.add(solverWithBehaviour)
		return solverWithBehaviour.behaviour.identifier
	}
}

open class SequentialSolverBuilder : SolverBuilder<SequentialBehaviour>() {
	protected lateinit var continuation: (assertions: List<Expression<Boolean>>, result: ContinuationResult, valuation: Valuation) -> ContinuationBuilder
	protected var useContext = false
	protected var enableUnsatCoreTracking = false

	fun continuation(func: (assertions: List<Expression<Boolean>>, result: ContinuationResult, valuation: Valuation) -> ContinuationBuilder) {
		continuation = func
	}

	fun useContext() {
		useContext = true
	}

	fun enableUnsatCoreTracking() {
		enableUnsatCoreTracking = true
	}

	override fun build(provIdentifier: String?): SolverWithBehaviour<SequentialBehaviour> {
		return SolverWithBehaviour(
			ConstraintSolverFactory.createSolver(provIdentifier, configuration),
			SequentialBehaviour(
				identifier = identifier,
				runIf = runIf,
				continuation = continuation,
				useContext = useContext,
				enableUnsatCore = enableUnsatCoreTracking,
			)
		)
	}
}

class SeqDslSolverBuilder : SequentialSolverBuilder() {
	private lateinit var solver: ConstraintSolver

	fun parallel(func: ParallelCompositionBuilder.() -> Unit) {
		solver = ParallelCompositionBuilder().apply(func).build()
	}

	fun sequential(func: SequentialCompositionBuilder.() -> Unit) {
		solver = SequentialCompositionBuilder().apply(func).build()
	}

	override fun build(provIdentifier: String?): SolverWithBehaviour<SequentialBehaviour> {
		return SolverWithBehaviour(
			solver, SequentialBehaviour(
				identifier = identifier,
				runIf = runIf,
				continuation = continuation,
				useContext = useContext,
				enableUnsatCore = enableUnsatCoreTracking,
			)
		)
	}
}

sealed class ContinuationBuilder(internal val continuation: Continuation) {

}

class DefaultContinuationBuilder(continuation: Continuation) : ContinuationBuilder(continuation)

sealed class SatReplacement

object AddValuation : SatReplacement()

object AddNegatedValuation : SatReplacement()

sealed class UnsatReplacement

object UnsatCore : UnsatReplacement()


class UnsatContinuationBuilder(continuation: Continuation) : ContinuationBuilder(continuation) {
	infix fun andReplaceAssertionsWith(replacement: UnsatReplacement): ContinuationBuilder {
		return DefaultContinuationBuilder(this.continuation.copy(replaceWithCore = true))
	}
}

class SatContinuationBuilder(continuation: Continuation) : ContinuationBuilder(continuation) {
	infix fun andAlterAssertions(replacement: SatReplacement): ContinuationBuilder {
		return DefaultContinuationBuilder(this.continuation.copy(replaceWithNewModel = true))
	}
}

sealed class ContinuationResult() {
	abstract fun stop(): ContinuationBuilder
	infix fun stopWith(result: ConstraintSolver.Result) = DefaultContinuationBuilder(Continuation(result))
	open infix fun continueWith(solverIdentifier: String) : ContinuationBuilder = DefaultContinuationBuilder(Continuation(result = ConstraintSolver.Result.DONT_KNOW, continueMode = Continue(solverIdentifier)))
}

object Unsat : ContinuationResult() {
	override infix fun continueWith(solverIdentifier: String): UnsatContinuationBuilder {
		return UnsatContinuationBuilder(
			Continuation(
				ConstraintSolver.Result.UNSAT,
				continueMode = Continue(solverIdentifier)
			)
		)
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.UNSAT))
}

object Sat : ContinuationResult() {
	override infix fun continueWith(solverIdentifier: String): SatContinuationBuilder {
		return SatContinuationBuilder(
			Continuation(
				ConstraintSolver.Result.SAT,
				continueMode = Continue(solverIdentifier)
			)
		)
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.SAT))
}

object DontKnow : ContinuationResult() {


	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.DONT_KNOW))
}

object Timeout : ContinuationResult() {


	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.TIMEOUT))
}

object Error : ContinuationResult() {


	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.ERROR))
}

object DidNotRun : ContinuationResult() {


	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.DONT_KNOW))
}

data class Continuation(
	val result: ConstraintSolver.Result,
	val continueMode: ContinueMode = Stop,
	val replaceWithCore: Boolean = false,
	val replaceWithNewModel: Boolean = false,
)

sealed class ContinueMode

object Stop : ContinueMode()

data class Continue(val identifier: String) : ContinueMode()