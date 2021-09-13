import tools.aqua.jconstraints.solvers.portfolio.sequential.StringOrFloatExpressionVisitor

class DSLPlayground {
	init {
		val cvcseqeval = SolverCompositionDSL.sequentialSolver {
			solver(Solver.CVC4) {
				timer = Time.minutes(1)
				name = "CVC4"
				runIf {
					it.accept(StringOrFloatExpressionVisitor(), null)
				}
				continueIf { expression, result, valuation ->
					when (result) {
						Result.SAT -> !expression.evaluateSMT(valuation)
						Result.UNSAT -> false
						Result.DONT_KNOW -> true
					}
				}
			}
			solver(Solver.Z3)
			finalVerdict { it.lastOrNull()?.second ?: Result.DONT_KNOW }
		}

		val majorityVote = SolverCompositionDSL.parallelSolver {
			solver(Solver.Z3)
			solver(Solver.CVC4)
			solver(cvcseqeval) {
				timer = Time.seconds(120)
				runIf {
					//hier könnte die expression untersucht werden
					true
				}
			}
			waitFor(3)
			finalVerdict { list ->
				list.groupBy { it.second }
					.maxByOrNull { it.value.size }?.key ?: Result.DONT_KNOW
			}
		}
	}
}