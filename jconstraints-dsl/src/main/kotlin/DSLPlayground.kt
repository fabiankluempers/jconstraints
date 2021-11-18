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

//
//import solverComposition.dsl.*
//import gov.nasa.jpf.constraints.api.ConstraintSolver
//import gov.nasa.jpf.constraints.api.Valuation
//import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
//import solverComposition.entity.SolverRunResult
//import solverComposition.entity.Time
//import tools.aqua.jconstraints.solvers.portfolio.sequential.StringOrFloatExpressionVisitor
//
//fun main() {
//	val parallelDontKnow = SolverCompositionDSL.parallelSolver {
//		solver(Solver.DONT_KNOW)
//	}
//	parallelDontKnow.solve(SMTProblem().allAssertionsAsConjunction, Valuation())
//}
//
//class DSLPlayground {
//	init {
//
//
//		val cvcSeqEval = SolverCompositionDSL.sequentialSolver {
//			solver(Solver.CVC4) {
//				timer = Time.minutes(1)
//				name = "CVC4"
//				runIf {
//					it.accept(StringOrFloatExpressionVisitor(), null)
//				}
//				continueIf { expression, result, valuation ->
//					when (result) {
//						SolverRunResult.SAT -> !expression.evaluateSMT(valuation)
//						SolverRunResult.UNSAT -> false
//						SolverRunResult.DONT_KNOW -> true
//						SolverRunResult.DID_NOT_RUN -> true
//					}
//				}
//			}
//			solver(Solver.Z3) {
//				name = "Z3"
//			}
//			finalVerdict {
//				val z3Result = it["Z3"]!!
//				val cvc4Result = it["CVC4"]!!
//				if (z3Result.ran()) z3Result.toResult() else cvc4Result.toResult()
//			}
//		}
//
//		val majorityVote = SolverCompositionDSL.parallelSolver {
//			solver(Solver.Z3) //adds a solver
//			solver(Solver.CVC4)
//			solver(cvcSeqEval) {
//				timer = Time.seconds(120)
//				name = "CVCSeqEval"
//				runIf {
//					true
//				}
//			}
//			//specify number of solvers that need to return a result before stopping the parallel composition.
//			waitFor(3)
//			finalVerdict { results ->
//				results
//					.map(Map.Entry<String, SolverRunResult>::value)
//					.filter(SolverRunResult::ran)
//					.groupBy { it }
//					.maxByOrNull { it.value.size }?.key?.toResult() ?: ConstraintSolver.Result.DONT_KNOW
//			}
//		}
//	}
//}