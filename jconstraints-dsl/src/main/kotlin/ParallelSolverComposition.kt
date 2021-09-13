import gov.nasa.jpf.constraints.api.Expression
import gov.nasa.jpf.constraints.api.Valuation

class ParallelSolver: SolverComposition() {
	private val solvers = mutableListOf<SolverComposition>()

	override fun solve(f: Expression<Boolean>?, result: Valuation?): Result {
		TODO("Not yet implemented")
	}
}