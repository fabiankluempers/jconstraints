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


import gov.nasa.jpf.constraints.api.*
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import solverComposition.dsl.*
import solverComposition.entity.ConstraintSolverComposition
import tools.aqua.jconstraints.solvers.portfolio.sequential.StringOrFloatExpressionVisitor
import java.time.Duration
import java.util.*
import kotlin.system.measureTimeMillis

fun main() {
	println(measureTimeMillis { (ConstraintSolverFactory.createSolver("seqtest").apply {
		val ctx = createContext()
		println(ctx.add(problem3.assertions))
		val valuation = Valuation()
		println(ctx.solve(valuation))
		println(valuation)
		ctx.dispose()
		ctx.add(problem4.assertions)
		println(ctx.solve(valuation))
		ctx.dispose()
		println(valuation)
		solve(problem3.allAssertionsAsConjunction, Valuation())
		solve(problem4.allAssertionsAsConjunction, Valuation())
	})})
}

val problem3: SMTProblem = SMTLIBParser.parseSMTProgram(
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

val problem4: SMTProblem = SMTLIBParser.parseSMTProgram(
	"""
	(declare-fun A () Int)
	(declare-fun B () Int)
	(assert (= A B))
	(assert (= A 5))
""".trimIndent()
)
