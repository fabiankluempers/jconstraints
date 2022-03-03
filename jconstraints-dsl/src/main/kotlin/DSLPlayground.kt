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
