import dsl.*
import tools.aqua.jconstraints.solvers.portfolio.sequential.StringOrFloatExpressionVisitor

class DSLPlayground {
	init {
		val cvcSeqEval = SolverCompositionDSL.sequentialSolver {
			solver(Solver.CVC4) {
				//specify how long the solver should run before being killed.
				timer = Time.minutes(1)
				//specify a name by which this solver is identified in the finalVerdict block.
				name = "CVC4"
				runIf {
					//specify whether to run this solver or not.
					//expression visiting can be done here.
					it.accept(StringOrFloatExpressionVisitor(), null)
				}
				continueIf { expression, result, valuation ->
					//specify based on the expression, result and valuation obtained from running this solver,
					//whether to continue or stop this sequential solver composition.
					when (result) {
						Result.SAT -> !expression.evaluateSMT(valuation)
						Result.UNSAT -> false
						Result.DONT_KNOW -> true
					}
				}
			}
			solver(Solver.Z3)
			//specify how a final verdict is obtained from individual solver runs.
			finalVerdict {
				it.lastOrNull()?.second ?: Result.DONT_KNOW
			}
		}

		val majorityVote = SolverCompositionDSL.parallelSolver {
			solver(Solver.Z3) //adds a solver
			solver(Solver.CVC4)
			solver(cvcSeqEval) {
				timer = Time.seconds(120)
				runIf {
					true
				}
			}
			//specify number of solvers that need to return a result before stopping the parallel composition.
			waitFor(3)
			finalVerdict { list ->
				list.groupBy { it.second }
					.maxByOrNull { it.value.size }?.key ?: Result.DONT_KNOW
			}
		}
	}
}