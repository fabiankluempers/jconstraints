package solverComposition.entity

import gov.nasa.jpf.constraints.api.ConstraintSolver
import java.util.concurrent.TimeUnit

enum class SolverRunResult {
	SAT,
	UNSAT,
	DONT_KNOW,
	DID_NOT_RUN;

	fun ran() = this != DID_NOT_RUN
	fun toResult() = when (this) {
		SAT -> ConstraintSolver.Result.SAT
		UNSAT -> ConstraintSolver.Result.UNSAT
		DONT_KNOW -> ConstraintSolver.Result.DONT_KNOW
		DID_NOT_RUN -> throw ClassCastException("Can not convert DID_NOT_RUN constant to a ${ConstraintSolver.Result::class}.")
	}
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


