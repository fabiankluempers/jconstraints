package dsl.instances

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.SolverCompositionDSL
import java.util.*

class ParallelTestSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("partest")

	override fun createSolver(config: Properties): ConstraintSolver =
		SolverCompositionDSL.parallelComposition {
			solver("mock") {
				identifier = "3000"
				configuration.setProperty("res", "sat")
				configuration.setProperty("timeout", "3000")
				ignoredSubset = setOf(ConstraintSolver.Result.SAT)
				useContext()
			}
			solver("mock") {
				identifier = "4000"
				configuration.setProperty("res", "sat")
				configuration.setProperty("timeout", "4000")
			}
			solver("mock") {
				identifier = "5000"
				configuration.setProperty("res", "sat")
				configuration.setProperty("timeout", "5000")
			}
			if (config.getProperty("run") == "par") {
				val limit = config.getProperty("lim")
				if (limit == null) {
					parallel()
				} else {
					parallelWithLimit(limit.toInt())
				}
			} else {
				sequential()
			}
			parallelWithLimit(5)
			finalVerdict { results ->
				println(results)
				results.values.first()
			}
		}
}