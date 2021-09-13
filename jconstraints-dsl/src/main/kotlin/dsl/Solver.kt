package dsl

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation

class Solver(identifier: String): SolverComposition() {
	lateinit var constraintSolver: ConstraintSolver

	//Todo respect timer
	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result = constraintSolver.solve(f, result)

	companion object {
		val Z3: Solver = Solver("Z3")
		val CVC4: Solver = Solver("CVC4")
	}
}