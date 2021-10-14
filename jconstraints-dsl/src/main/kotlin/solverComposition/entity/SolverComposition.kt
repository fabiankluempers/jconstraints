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
import java.util.concurrent.TimeUnit

enum class SolverRunResult {
	SAT,
	UNSAT,
	DONT_KNOW,
	DID_NOT_RUN;

	fun ran() = this != DID_NOT_RUN
	fun toResult() = when (this) {
		SAT -> ConstraintSolver.Result.SAT
		UNSAT -> ConstraintSolver.Result.UNSAT
		DONT_KNOW -> ConstraintSolver.Result.DONT_KNOW
		DID_NOT_RUN -> throw ClassCastException("Can not convert DID_NOT_RUN constant to a ${ConstraintSolver.Result::class}.")
	}
}

data class Time(val unit: TimeUnit, val value: Int) {
	companion object {
		fun nanoseconds(value: Int) = Time(unit = TimeUnit.NANOSECONDS, value)
		fun milliseconds(value: Int) = Time(unit = TimeUnit.MILLISECONDS, value)
		fun seconds(value: Int) = Time(unit = TimeUnit.SECONDS, value)
		fun minutes(value: Int) = Time(unit = TimeUnit.MINUTES, value)
	}
}

abstract class SolverComposition: ConstraintSolver() {
	lateinit var timer: Time
}


