import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver
import java.util.concurrent.TimeUnit

enum class Result {
	SAT,
	UNSAT,
	DONT_KNOW
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


