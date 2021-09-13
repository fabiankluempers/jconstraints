package dsl

import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation

class SolverCompositionDSL {
	companion object {
		fun sequentialSolver(func: SequentialSolverCompositionBuilder.() -> Unit) : SolverComposition {
			return SequentialSolver()
		}
		fun parallelSolver(func: ParallelSolverCompositionBuilder.() -> Unit) : SolverComposition {
			return ParallelSolver()
		}
	}
}

//region sequential
class SequentialSolverCompositionBuilder(){

}

class SequentialSolverBuilder(){
	lateinit var timer: Time
	lateinit var name: String
}

fun SolverCompositionDSL.sequentialSolver(func: SequentialSolverCompositionBuilder.() -> Unit) : SolverComposition {
	return SequentialSolver()
}

fun SequentialSolverCompositionBuilder.solver(solver : SolverComposition, func: SequentialSolverBuilder.() -> Unit = {}) {

}

fun SequentialSolverCompositionBuilder.finalVerdict(func: (solverResults : List<Pair<String, Result>>) -> Result) {

}

fun SequentialSolverBuilder.runIf(func: (expression: Expression<Boolean>) -> Boolean) {

}

fun SequentialSolverBuilder.continueIf(func: (expression: Expression<Boolean>, result : Result, valuation: Valuation) -> Boolean) {

}
//endregion

//region parallel
class ParallelSolverCompositionBuilder() {
	lateinit var timer: Time
}


class ParallelSolverBuilder() {
	lateinit var name: String
}

fun ParallelSolverCompositionBuilder.solver(solver : SolverComposition, func: ParallelSolverBuilder.() -> Unit = {}) {

}

fun ParallelSolverCompositionBuilder.finalVerdict(func: (solverResults : List<Pair<String, Result>>) -> Result) {

}

fun ParallelSolverCompositionBuilder.waitFor(numberOfSolvers: Int) {

}

fun ParallelSolverBuilder.runIf(func: (expression: Expression<Boolean>) -> Boolean) {

}
//endregion
