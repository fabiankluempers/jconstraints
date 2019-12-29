package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.math.BigDecimal;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;

public class RegExBooleanExpression extends AbstractBoolExpression {
	public static RegExBooleanExpression create (Expression<?> left,Expression<?> right) {
		return new RegExBooleanExpression(left,right);
	}
	private final Expression<?> left;
	private final Expression<?> right;
	public RegExBooleanExpression(Expression<?> left,Expression<?> right) {
		this.left=left;
		this.right=right;
	}
	
	public Expression<?> getLeft() {
	    return this.left;
	}
	
	public Expression<?> getRight(){
		return this.right;
	}
	@Override
	public Boolean evaluate(Valuation values) {
		//throw new UnsupportedOperationException();
		return null;
	}


	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		return visitor.visit(this, data);		
	}

	@Override
	public Expression<?>[] getChildren() {
		return new Expression[]{left, right};
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		assert newChildren.length == 2;
	    Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
	    if(left == newLeft && right == newRight)
	      return this;
	    return new RegExBooleanExpression(newLeft,newRight);
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		a.append('(');
		right.print(a, flags);
		a.append(" MATCHES: ");
		left.print(a,flags);
		a.append(')');

	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		//throw new UnsupportedOperationException();

	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
	    this.left.collectFreeVariables(variables);
	    this.right.collectFreeVariables(variables);
	}
	

}
