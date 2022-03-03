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