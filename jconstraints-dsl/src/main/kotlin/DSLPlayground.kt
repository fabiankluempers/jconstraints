import tools.aqua.jconstraints.solvers.portfolio.sequential.StringOrFloatExpressionVisitor

class DSLPlayground {
	init {
		val cvcseqeval = SolverCompositionDSL.sequentialSolver {
			solver(Solver.CVC4) {
				timer = Time.minutes(1)
				name = "CVC4"
				runIf<Boolean> {
					it.accept(StringOrFloatExpressionVisitor(), null)
				}
				evaluate<Boolean> { expression, result, valuation ->
					when (result) {
						Result.SAT -> if (expression.evaluateSMT(valuation)) Sequential.STOP else Sequential.CONTINUE
						Result.UNSAT -> Sequential.STOP
						Result.DONT_KNOW -> Sequential.CONTINUE
					}
				}
			}
			solver(Solver.Z3) {
				name = "Z3"
			}
			finalVerdict {
				it.lastOrNull()?.second ?: Result.DONT_KNOW
			}
		}
	}
}