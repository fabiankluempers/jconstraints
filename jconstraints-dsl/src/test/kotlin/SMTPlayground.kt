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
import gov.nasa.jpf.constraints.api.UNSATCoreSolver
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory

class SMTPlayground {

}

//fun main() {
//	val problem = SMTLIBParser.parseSMTProgram(
//		"""
//			(declare-fun I0_2 () Int)
//			(declare-fun I1_2 () Int)
//			(declare-fun I2_2 () Int)
//			(declare-fun PCTEMP_LHS_1 () String)
//			(declare-fun T1_2 () String)
//			(declare-fun T2_2 () String)
//			(declare-fun T3_2 () String)
//			(declare-fun T_2 () Bool)
//			(declare-fun var_0xINPUT_2 () String)
//			(assert (= I0_2 (- 5 0)))
//			(assert (>= 0 0))
//			(assert (>= 5 0))
//			(assert (<= 5 I1_2))
//			(assert (= I2_2 I1_2))
//			(assert (= I0_2 (str.len PCTEMP_LHS_1)))
//			(assert (= var_0xINPUT_2 (str.++ T1_2 T2_2)))
//			(assert (= T2_2 (str.++ PCTEMP_LHS_1 T3_2)))
//			(assert (= 0 (str.len T1_2)))
//			(assert (= I1_2 (str.len var_0xINPUT_2)))
//			(assert (= T_2 (not (= PCTEMP_LHS_1 "hello"))))
//			(assert T_2)
//			(check-sat)
//			""".trimIndent()
//	).allAssertionsAsConjunction
//	val problem2 = SMTLIBParser.parseSMTProgram(
//		"""
//			(declare-fun A () Int)
//			(declare-fun B () Int)
//			(declare-fun C () Int)
//			(assert (> A B))
//			(assert (= A B))
//			(assert (= B 5))
//			(assert (= A 5))
//			(assert (= C 7))
//			(check-sat)
//		""".trimIndent()
//	)
////	println(problem2.variables)
////	println(problem2.allAssertionsAsConjunction)
//
//	val z3 = ConstraintSolverFactory.createSolver("z3")
//	(z3 as UNSATCoreSolver).enableUnsatTracking()
//	val ctx = z3.createContext()
//
//	val p = Variable.create(BuiltinTypes.SINT32, "p")
//	val q = Variable.create(BuiltinTypes.SINT32, "q")
//
//	val peqq = NumericBooleanExpression.create(p, NumericComparator.EQ, q)
//	val pgtq = NumericBooleanExpression.create(p, NumericComparator.GT, q)
//	val conj = PropositionalCompound.create(peqq, LogicalOperator.AND, pgtq)
//
//	ctx.add(problem2.assertions)
//
//	val valuation = Valuation()
//
//	println(ctx.solve(valuation))
//
//	println(valuation)
//
//	//println(problem2.allAssertionsAsConjunction.evaluateSMT(valuation))
//
//	if (ctx is UNSATCoreSolver) {
//		println("core: ${ctx.unsatCore}")
//	}
//
////	if (z3 is UNSATCoreSolver) {
////		z3.enableUnsatTracking()
////		val valuation = Valuation()
////		val valuation2 = Valuation()
////		val res = z3.solve(problem2, valuation)
////		val res2 = z3.solve(problem, valuation2)
////		println("res: $res")
////		println(valuation)
////		if (res == ConstraintSolver.Result.UNSAT) {
////			val core = z3.unsatCore
////			println(core.size)
////		}
////		println("res2: $res2")
////		println(valuation2)
////		if (res2 == ConstraintSolver.Result.UNSAT) {
////			val core = z3.unsatCore
////			println(core.size)
////		}
////	}
//}


val problem: SMTProblem = SMTLIBParser.parseSMTProgram(
	"""
			(declare-fun A () Int)
			(declare-fun B () Int)
			(declare-fun C () Int)
			(assert (= (* A B) C))
			(assert (= C 932067827))
			(assert (not (= 1 A)))
			(assert (not (= 1 B)))
			(assert (>= A 0))
			(assert (>= B 0))
			(check-sat)
		""".trimIndent()
)

val problem2: SMTProblem = SMTLIBParser.parseSMTProgram(
	"""
	(declare-fun A () Int)
	(declare-fun B () Int)
	(declare-fun C () Int)
	(assert (= A B))
	(assert (> A B))
	(assert (> C A))
	(assert (= C 5))
	(check-sat)
	""".trimIndent()
)

fun main() {
	val solver = ConstraintSolverFactory.createSolver("z3")
	val valuation = Valuation()
	if (solver is UNSATCoreSolver) {
		solver.enableUnsatTracking()
		println(problem2)
		println(solver.solve(problem2.allAssertionsAsConjunction, valuation))
		println(valuation)
		println(solver.unsatCore)
	}
	val ctx = solver.createContext()
	if (ctx is UNSATCoreSolver) {
		ctx.enableUnsatTracking()
		problem2.addProblemToContext(ctx)
		val res = ctx.solve(valuation)
		println(valuation)
		println(ctx.unsatCore)
		if (res == ConstraintSolver.Result.UNSAT)
	}
}

fun withCtxAndConj(problem: SMTProblem) {
	val z3 = ConstraintSolverFactory.createSolver("z3")
	(z3 as UNSATCoreSolver).enableUnsatTracking()
	val ctx = z3.createContext()

	val valuation = Valuation()
	ctx.add(problem.allAssertionsAsConjunction)
	val res = ctx.solve(valuation)
	println("res: $res")
	println("valuation: $valuation")

	if (res == ConstraintSolver.Result.UNSAT) {
		println("core: ${(ctx as UNSATCoreSolver).unsatCore}")
	}
}

fun withCtxAndIndividualAssertions(problem: SMTProblem) {
	val z3 = ConstraintSolverFactory.createSolver("z3")
	(z3 as UNSATCoreSolver).enableUnsatTracking()
	val ctx = z3.createContext()

	val valuation = Valuation()
	ctx.add(problem.assertions)
	val res = ctx.solve(valuation)
	println("res: $res")
	println("valuation: $valuation")

	if (res == ConstraintSolver.Result.UNSAT) {
		println("core: ${(ctx as UNSATCoreSolver).unsatCore}")
	}
}