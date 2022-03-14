package test

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.SolverCompositionDSL
import java.util.*

class TestSequentialCompositionProvider() : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("test seq prov")

	override fun createSolver(config: Properties?): ConstraintSolver = SolverCompositionDSL.sequentialComposition {
		solver("mock") {
			identifier = "mock"
			continuation { _, result, _ -> result.stop() }
		}
		startWith { "mock" }
	}
}