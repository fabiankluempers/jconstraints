import dsl.*
import gov.nasa.jpf.constraints.api.ConstraintSolver
import solverComposition.entity.SolverRunResult
import solverComposition.entity.Solver
import solverComposition.entity.Time
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
						SolverRunResult.SAT -> !expression.evaluateSMT(valuation)
						SolverRunResult.UNSAT -> false
						SolverRunResult.DONT_KNOW -> true
						SolverRunResult.DID_NOT_RUN -> true
					}
				}
			}
			solver(Solver.Z3) {
				name = "Z3"
			}
			//specify how a final verdict is obtained from individual solver runs.
			finalVerdict {
				val z3Result = it["Z3"]!!
				val cvc4Result = it["CVC4"]!!
				if (z3Result.ran()) z3Result.toResult() else cvc4Result.toResult()
			}
		}

		val majorityVote = SolverCompositionDSL.parallelSolver {
			solver(Solver.Z3) //adds a solver
			solver(Solver.CVC4)
			solver(cvcSeqEval) {
				timer = Time.seconds(120)
				name = "CVCSeqEval"
				runIf {
					true
				}
			}
			//specify number of solvers that need to return a result before stopping the parallel composition.
			waitFor(3)
			finalVerdict { results ->
				results
					.map(Map.Entry<String, SolverRunResult>::value)
					.filter(SolverRunResult::ran)
					.groupBy { it }
					.maxByOrNull { it.value.size }?.key?.toResult() ?: ConstraintSolver.Result.DONT_KNOW
			}
		}
	}
}