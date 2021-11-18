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
//
//import gov.nasa.jpf.constraints.api.ConstraintSolver
//import gov.nasa.jpf.constraints.api.Expression
//import gov.nasa.jpf.constraints.api.Valuation
//import solverComposition.entity.*
//
//object SolverCompositionDSL {
//
//	fun sequentialSolver(func: SequentialSolverCompositionBuilder.() -> Unit): ConstraintSolver {
//		return SequentialSolver()
//	}
//
//	fun parallelSolver(func: ParallelSolverCompositionBuilder.() -> Unit): ConstraintSolver {
//		return ParallelSolver()
//	}
//
//}
//
////region sequential
//class SequentialSolverCompositionBuilder() {
//
//}
//
//sealed class SequentialSolverBuilder() {
//	lateinit var timer: Time
//	lateinit var name: String
//}
//
//fun SequentialSolverCompositionBuilder.solver(
//	solver: ConstraintSolver,
//	func: SequentialSolverBuilder.() -> Unit = {}
//) {
//
//}
//
//fun SequentialSolverCompositionBuilder.finalVerdict(func: (solverResults: Map<String, SolverRunResult>) -> ConstraintSolver.Result) {
//
//}
//
//fun SequentialSolverBuilder.runIf(func: (expression: Expression<Boolean>) -> Boolean) {
//
//}
//
//fun SequentialSolverBuilder.continueIf(func: (expression: Expression<Boolean>, solverRunResult: SolverRunResult, valuation: Valuation) -> Boolean) {
//
//}
//
//fun SequentialSolverBuilder.enableFeatures(func: FeatureBlock.() -> Unit) {
//
//}
//
//class FeatureBlock {
//
//}
//
//fun FeatureBlock.unsatCoreTracking(): UnsatCoreTrackingFeature {
//	return UnsatCoreTrackingFeature()
//}
//
//class UnsatCoreTrackingFeature {
//	infix fun force(flag: Boolean) {
//
//	}
//}
//
//
//fun FeatureBlock.negatedValuation() {
//
//}
////endregion
//
////region parallel
//class ParallelSolverCompositionBuilder() {
//	lateinit var timer: Time
//}
//
//class ParallelSolverBuilder() {
//	lateinit var name: String
//}
//
//fun ParallelSolverCompositionBuilder.solver(solver: ConstraintSolver, func: ParallelSolverBuilder.() -> Unit = {}) {
//
//}
//
//fun ParallelSolverCompositionBuilder.finalVerdict(func: (solverResults: Map<String, SolverRunResult>) -> ConstraintSolver.Result) {
//
//}
//
//fun ParallelSolverCompositionBuilder.waitFor(numberOfSolvers: Int) {
//
//}
//
//fun ParallelSolverBuilder.runIf(func: (expression: Expression<Boolean>) -> Boolean) {
//
//}
////endregion
