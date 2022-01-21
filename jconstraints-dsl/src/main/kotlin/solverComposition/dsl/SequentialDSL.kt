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
import java.util.*

class SequentialCompositionBuilder : CompositionBuilder<SequentialSolverBuilder>() {
	private val solvers = mutableMapOf<String, SolverWithBehaviour<SequentialBehaviour>>()
	private lateinit var startWith: (assertions: List<Expression<Boolean>>) -> String

	override fun build(): ConstraintSolver {
		return SequentialComposition(solvers, startWith)
	}

	fun startWith(func: (assertions: List<Expression<Boolean>>) -> String) {
		startWith = func
	}

	override fun solver(solver: String, func: SequentialSolverBuilder.() -> Unit) {
		val behaviour = SequentialSolverBuilder().apply(func).build()
		solvers[behaviour.identifier] = SolverWithBehaviour(ConstraintSolverFactory.createSolver(solver, behaviour.config), behaviour)
	}
}

class SequentialSolverBuilder : SolverBuilder<SequentialBehaviour>() {
	private lateinit var continuation: (assertions: List<Expression<Boolean>>, result: ContinuationResult, valuation: Valuation) -> ContinuationBuilder
	private var useContext = false
	private var enableUnsatCoreTracking = false
	var config: Properties = Properties()

	fun continuation(func: (assertions: List<Expression<Boolean>>, result: ContinuationResult, valuation: Valuation) -> ContinuationBuilder) {
		continuation = func
	}

	fun useContext() {
		useContext = true
	}

	fun enableUnsatCoreTracking() {
		enableUnsatCoreTracking = true
	}

	override fun build(): SequentialBehaviour {
		return SequentialBehaviour(
			identifier = identifier,
			runIf = runIf,
			continuation = continuation,
			useContext = useContext,
			enableUnsatCore = enableUnsatCoreTracking,
			config = config
		)
	}
}

sealed class ContinuationBuilder(internal val continuation: Continuation) {

}

class DefaultContinuationBuilder(continuation: Continuation) : ContinuationBuilder(continuation)

object UnsatCore

object NewModel

class UnsatContinuationBuilder(continuation: Continuation) : ContinuationBuilder(continuation) {
	infix fun andReplaceWith(core: UnsatCore): ContinuationBuilder {
		return DefaultContinuationBuilder(this.continuation.copy(replaceWithCore = true))
	}
}

class SatContinuationBuilder(continuation: Continuation) : ContinuationBuilder(continuation) {
	infix fun andReplaceWith(newModel: NewModel): ContinuationBuilder {
		return DefaultContinuationBuilder(this.continuation.copy(replaceWithNewModel = true))
	}
}

sealed class ContinuationResult() {
	abstract fun stop(): ContinuationBuilder
}

object Unsat : ContinuationResult() {
	infix fun continueWith(solverIdentifier: String): UnsatContinuationBuilder {
		return UnsatContinuationBuilder(Continuation(ConstraintSolver.Result.UNSAT, continueMode = Continue(solverIdentifier)))
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.UNSAT))
}

object Sat : ContinuationResult() {
	infix fun continueWith(solverIdentifier: String): SatContinuationBuilder {
		return SatContinuationBuilder(Continuation(ConstraintSolver.Result.SAT, continueMode = Continue(solverIdentifier)))
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.SAT))
}

object DontKnow : ContinuationResult() {
	infix fun continueWith(solverIdentifier: String): ContinuationBuilder {
		return DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.DONT_KNOW, continueMode = Continue(solverIdentifier)))
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.DONT_KNOW))
}

object Timeout : ContinuationResult() {
	infix fun continueWith(solverIdentifier: String): ContinuationBuilder {
		return DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.TIMEOUT, continueMode = Continue(solverIdentifier)))
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.TIMEOUT))
}

object Error : ContinuationResult() {
	infix fun continueWith(solverIdentifier: String): ContinuationBuilder {
		return DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.ERROR, continueMode = Continue(solverIdentifier)))
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.ERROR))
}

object DidNotRun : ContinuationResult() {
	infix fun continueWith(solverIdentifier: String): ContinuationBuilder {
		return DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.DONT_KNOW, continueMode = Continue(solverIdentifier)))
	}

	override fun stop(): ContinuationBuilder =
		DefaultContinuationBuilder(Continuation(ConstraintSolver.Result.DONT_KNOW))
}

data class Continuation(
	val result: ConstraintSolver.Result,
	val continueMode: ContinueMode = Stop,
	val replaceWithCore: Boolean = false,
	val replaceWithNewModel: Boolean = false,
)

sealed class ContinueMode()

object Stop : ContinueMode()

data class Continue(val identifer: String) : ContinueMode()