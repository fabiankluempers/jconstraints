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

import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor
import gov.nasa.jpf.constraints.expressions.NumericCompound
import gov.nasa.jpf.constraints.expressions.NumericOperator

class IsMulExpressionVisitor :
	AbstractExpressionVisitor<Boolean, Unit>() {

	override fun <E : Any?> visit(
		n: NumericCompound<E>,
		data: Unit?,
	): Boolean {
		return when (n.operator) {
			NumericOperator.MUL -> true
			else -> false
		}
	}

	override fun <E : Any?> defaultVisit(
		expression: Expression<E>,
		data: Unit?,
	): Boolean {
		return expression.children.any { child ->
			child.accept(this, null)
		}
	}
}
