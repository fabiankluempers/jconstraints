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

package test

import gov.nasa.jpf.constraints.api.ConstraintSolver
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import solverComposition.dsl.*

internal class ContinuationTest {

	@Test
	fun testUnsatContinueReplace() {
		val actual = (Unsat continueWith "id" andReplaceAssertionsWith UnsatCore).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.UNSAT,
			continueMode = Continue("id"),
			replaceWithCore = true,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testUnsatContinue() {
		val actual = (Unsat continueWith "id").continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.UNSAT,
			continueMode = Continue("id"),
			replaceWithCore = false,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testUnsatStop() {
		val actual = (Unsat.stop()).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.UNSAT,
			continueMode = Stop,
			replaceWithCore = false,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testSatContinueReplace() {
		val actual = (Sat continueWith "id" andAlterAssertions AddNegatedValuation).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.SAT,
			continueMode = Continue("id"),
			replaceWithCore = false,
			replaceWithNewModel = true,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testSatContinue() {
		val actual = (Sat continueWith "id" andAlterAssertions AddNegatedValuation).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.SAT,
			continueMode = Continue("id"),
			replaceWithCore = false,
			replaceWithNewModel = true,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testSatStop() {
		val actual = (Sat.stop()).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.SAT,
			continueMode = Stop,
			replaceWithCore = false,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}
}