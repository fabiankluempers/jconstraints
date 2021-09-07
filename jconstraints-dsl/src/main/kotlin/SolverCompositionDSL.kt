import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation

class SolverCompositionDSL {
	companion object {
		fun sequentialSolver(func: SequentialSolverCompositionBuilder.() -> Unit) : SolverComposition {
			return SequentialSolver()
		}
	}
}

enum class Sequential {
	STOP,
	CONTINUE,
}

class SequentialSolverCompositionBuilder(){
	var name: String = ""
}

class SequentialSolverBuilder(){
	var timer: Time = Time.seconds(0)
}

fun SolverCompositionDSL.sequentialSolver(func: SequentialSolverCompositionBuilder.() -> Unit) : SolverComposition {
	return SequentialSolver()
}

fun SequentialSolverCompositionBuilder.solver(solver : Solver, func: SequentialSolverBuilder.() -> Unit = {}) {

}

fun SequentialSolverCompositionBuilder.finalVerdict( func: (solverResults : List<Pair<String, Result>>) -> Result) {

}

fun <T> SequentialSolverBuilder.runIf(func: (expression: Expression<T>) -> Boolean) {

}

fun <T> SequentialSolverBuilder.evaluate(func: (expression: Expression<T>, result : Result, valuation: Valuation) -> Sequential) {

}
