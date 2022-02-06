package instances

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider
import solverComposition.dsl.SolverCompositionDSL
import solverComposition.entity.DSLResult
import java.util.*

class ParallelTestSolverProvider : ConstraintSolverProvider {
	override fun getNames(): Array<String> = arrayOf("partest")

	override fun createSolver(config: Properties): ConstraintSolver =
		SolverCompositionDSL.parallelComposition {
			solver("mock") {
				identifier = "3000"
				conf.setProperty("res", "sat")
				conf.setProperty("timeout", "3000")
				ignoredSubset = setOf(ConstraintSolver.Result.SAT)
			}
			solver("mock") {
				identifier = "2000"
				conf.setProperty("res", "sat")
				conf.setProperty("timeout", "2000")
			}
			dslSolver {

				parallel {
					solver("dontKnow") {
						runIf {
							println("inner DK starting!!")
							true
						}
						useContext()
						identifier = "dk"
					}

					finalVerdict {
						println("inner DK stopping!!")
						DSLResult(ConstraintSolver.Result.DONT_KNOW, Valuation())
					}

					sequential()
				}

				identifier = "inner dsl solver"
				useContext()

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
			finalVerdict { results ->
				println(results)
				results.values.first()
			}
		}
}