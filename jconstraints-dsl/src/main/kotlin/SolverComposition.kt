import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver
import java.util.concurrent.TimeUnit

enum class Result {
	SAT,
	UNSAT,
	DONT_KNOW
}

class Time(val unit: TimeUnit, val value: Int) {
	companion object {
		fun nanoseconds(value: Int) = Time(unit = TimeUnit.NANOSECONDS, value)
		fun milliseconds(value: Int) = Time(unit = TimeUnit.MILLISECONDS, value)
		fun seconds(value: Int) = Time(unit = TimeUnit.SECONDS, value)
		fun minutes(value: Int) = Time(unit = TimeUnit.MINUTES, value)
	}
}

abstract class SolverComposition {
	lateinit var timer: Time
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
