package instances

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import java.util.*

class MockSolver(private val res: Result, private val runtime: Long) : ConstraintSolver() {
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		try {
			Thread.sleep(runtime)
		} catch (e : InterruptedException) {
			println("mock solver was interrupted")
			return res
		}
		println("mock solver was not interrupted")
		return res
	}
}

class MockSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("Mock", "mock")

	override fun createSolver(config: Properties): ConstraintSolver {
		val actualResult = when (config.getProperty("res", "unknown")) {
			"sat" -> ConstraintSolver.Result.SAT
			"unsat" -> ConstraintSolver.Result.UNSAT
			"unknown" -> ConstraintSolver.Result.DONT_KNOW
			"error" -> ConstraintSolver.Result.ERROR
			"timeout" -> ConstraintSolver.Result.TIMEOUT
			else -> ConstraintSolver.Result.UNSAT
		}
		return MockSolver(actualResult, config.getProperty("timeout", "0").toLong())
	}
}