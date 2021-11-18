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
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation

class TestSatSolver : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		return Result.SAT
	}
}

class TestUnsatSolver : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		return Result.UNSAT
	}
}

class TestDontKnowSolver : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		return Result.DONT_KNOW
	}
}

class TestErrorSolver : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		return Result.ERROR
	}
}

class TestTimeoutSolver : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		return Result.TIMEOUT
	}

}