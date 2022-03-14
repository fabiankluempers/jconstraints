package test

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.SolverCompositionDSL
import java.util.*

class TestParallelCompositionProvider() : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("test par prov")

	override fun createSolver(config: Properties?): ConstraintSolver = SolverCompositionDSL.parallelComposition {
		parallelWithLimit(1)
		solver("mock") { identifier = "mock"; ignoredSubset = setOf(ConstraintSolver.Result.ERROR)}
		finalVerdict { it.values.first() }
	}
}