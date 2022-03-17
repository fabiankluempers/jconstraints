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
import solverComposition.entity.ParallelBehaviour
import solverComposition.entity.SolverWithBehaviour

class ParDslSolverBuilder : ParallelSolverBuilder() {
	private lateinit var solver: ConstraintSolver

	fun parallel(func: ParallelCompositionBuilder.() -> Unit) {
		solver = ParallelCompositionBuilder().apply(func).build()
	}

	fun sequential(func: SequentialCompositionBuilder.() -> Unit) {
		solver = SequentialCompositionBuilder().apply(func).build()
	}

	override fun build(provIdentifier: String?): SolverWithBehaviour<ParallelBehaviour> {
		return SolverWithBehaviour(
			solver, ParallelBehaviour(
				identifier = identifier,
				runIf = runIf,
				useContext = useContext,
				ignoredSubset = ignoredSubset
			)
		)
	}
}