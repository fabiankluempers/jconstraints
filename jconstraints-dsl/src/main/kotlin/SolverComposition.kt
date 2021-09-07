import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver
import java.util.concurrent.TimeUnit

class Timer(val unit: TimeUnit, val value: Int) {

}

abstract class SolverComposition {
	lateinit var timer: Timer
}

class ParallelSolverComposition: SolverComposition() {
	private val solvers = mutableListOf<SolverComposition>()
}

class SequentialSolver: SolverComposition() {
	private val solvers = mutableListOf<SolverComposition>()
}

class Solver: SolverComposition() {
	private var constraintSolver: ConstraintSolver? = null //TODO make nullsafe

	companion object {
		val Z3 : Solver = Solver().apply {
			constraintSolver = ConstraintSolverFactory.createSolver("Z3")
		}
		val CVC4 : Solver = Solver().apply {
			constraintSolver = ProcessWrapperSolver("cvc4")
		}
	}
}
