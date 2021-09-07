import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation

class SolverCompositionDSL

class SequentialSolverCompositionBuilder(){

}

class SequentialSolverBuilder(){

}

fun SolverCompositionDSL.sequentialSolver(func: SequentialSolverCompositionBuilder.() -> Unit) : SolverComposition {
	return SequentialSolver()
}

fun SequentialSolverCompositionBuilder.solver(solver : Solver, func: SequentialSolverBuilder.() -> Unit) {

}

fun SequentialSolverCompositionBuilder.finalVerdict( func: (solverResults : Map<String,ConstraintSolver.Result>) -> ConstraintSolver.Result) {

}

fun <T> SequentialSolverBuilder.before(func: (expression: Expression<T>) -> Unit) {

}

fun <T> SequentialSolverBuilder.after(func: (expression: Expression<T>, result : ConstraintSolver.Result, valuation: Valuation) -> Unit) {

}
