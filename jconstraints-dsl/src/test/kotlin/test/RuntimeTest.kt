package test

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.UNSATCoreSolver
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import gov.nasa.jpf.constraints.util.ExpressionUtil
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import solverComposition.dsl.Sat
import solverComposition.dsl.SolverCompositionDSL
import solverComposition.dsl.Unsat
import solverComposition.dsl.UnsatCore
import solverComposition.entity.DSLResult
import kotlin.system.measureTimeMillis

val unsatProblem: SMTProblem = SMTLIBParser.parseSMTProgram(
	"""
			(declare-fun A () Int)
			(declare-fun B () Int)
			(declare-fun C () Int)
			(assert (= A B))
			(assert (> A B))
			(assert (> C A))
			(assert (= C 5))
			(check-sat)
		""".trimIndent()
)

val satProblem: SMTProblem = SMTLIBParser.parseSMTProgram(
	"""
	(declare-fun A () Int)
	(declare-fun B () Int)
	(assert (= A B))
	(assert (= A 5))
""".trimIndent()
)

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SeqRuntimeTest {
	@BeforeAll
	fun initialLoad() {
		ConstraintSolverFactory.createSolver("z3")
		ConstraintSolverFactory.createSolver("dontKnow")
		ConstraintSolverFactory.createSolver("mock")
	}

	private fun genSeqMockComp(numMocks : Int) = SolverCompositionDSL.sequentialComposition {
		startWith { "mock1" }
		repeat(numMocks) {
			solver("mock") {
				identifier = "mock$it"
				configuration["res"] = "sat"
				continuation { _, result, _ ->
					when(result) {
						is Sat -> result continueWith "mock${it+1}"
						else -> result stopWith ConstraintSolver.Result.DONT_KNOW
					}
				}
			}
		}
		solver("mock") {
			identifier = "mock$numMocks"
			continuation { _, result, _ ->
				result.stop()
			}
		}
	}

	private fun genParMockComp() = SolverCompositionDSL.parallelComposition {
		parallelWithLimit(2501)
		//valid results
		repeat(2500) {
			solver("mock") {
				identifier = "mock$it"
				configuration["res"] = "sat"
			}
		}
		//result in ignored subset
		repeat(2500) {
			solver("mock") {
				identifier = "mock${it+2500}"
				configuration["res"] = "sat"
				ignoredSubset = setOf(ConstraintSolver.Result.SAT)
			}
		}
		//runtime of 1s
		repeat(2500) {
			solver("mock") {
				identifier = "mock${it+5000}"
				configuration["res"] = "sat"
				configuration["timeout"] = "1000"
			}
		}
		//runtime of 10s
		repeat(2500) {
			solver("mock") {
				identifier = "mock${it+7500}"
				configuration["res"] = "sat"
				configuration["timeout"] = "10000"
			}
		}
		finalVerdict { results ->
			results.values.first()
		}
	}

	@Test fun test10kMocksSeq() {
		var comp: ConstraintSolver?
		val timeSpentLoading = measureTimeMillis {
			comp = genSeqMockComp(10000)
		}
		val assertion = satProblem.allAssertionsAsConjunction
		val timeSpentSolving = measureTimeMillis {
			comp?.solve(assertion, Valuation())
		}
		println("test10kMocksSeq: time spent loading 10k mock solvers: $timeSpentLoading, time spent solving with 10k mock solvers: $timeSpentSolving")
	}

	@Test fun test10kMocksPar() {
		var comp: ConstraintSolver?
		val timeSpentLoading = measureTimeMillis {
			comp = genParMockComp()
		}
		val assertion = satProblem.allAssertionsAsConjunction
		val timeSpentSolving = measureTimeMillis {
			comp?.solve(assertion, Valuation())
		}
		println("test10kMocksPar: time spent loading 10k mock solvers: $timeSpentLoading, time spent solving with 10k mock solvers: $timeSpentSolving")
	}

	@Test fun testZ3inSeq() {
		val comp = SolverCompositionDSL.sequentialComposition {
			startWith { "Z3" }
			solver("Z3") {
				identifier = "Z3"
				useContext()
				enableUnsatCoreTracking()
				continuation { assertions, result, valuation ->
					when (result) {
						is Sat -> result stopWith ConstraintSolver.Result.SAT
						is Unsat -> result continueWith "dk" andReplaceAssertionsWith UnsatCore
						else -> result stopWith ConstraintSolver.Result.DONT_KNOW
					}
				}
			}
			solver("dontKnow") {
				identifier = "dk"
				continuation { _, result, _, ->
					result.stop()
				}
			}
		}
		val ctx = comp.createContext()
		val timeSpentSat = measureTimeMillis {
			ctx.push()
			ctx.add(satProblem.assertions)
			ctx.solve(Valuation())
			ctx.pop()
		}
		println("testZ3inSeq: time spent solving sat instance: $timeSpentSat")
		val timeSpentUnsat = measureTimeMillis {
			ctx.push()
			ctx.add(unsatProblem.assertions)
			ctx.solve(Valuation())
			ctx.pop()
		}
		println("testZ3inSeq: time spent solving unsat instance: $timeSpentUnsat")
	}

	@Test fun testNoDSL() {
		val z3 = ConstraintSolverFactory.createSolver("z3")
		val dk = ConstraintSolverFactory.createSolver("z3")
		val z3ctx = z3.createContext()
		val z3unsatSolver = (z3ctx as UNSATCoreSolver)
		z3unsatSolver.enableUnsatTracking()
		val timeSpentSat = measureTimeMillis {
			z3ctx.push()
			z3ctx.add(satProblem.assertions)
			z3ctx.solve(Valuation())
			z3ctx.pop()
			dk.solve(satProblem.allAssertionsAsConjunction, Valuation())
		}
		println("testNoDSL: time spent solving sat instance: $timeSpentSat")
		val timeSpentUnsat = measureTimeMillis {
			z3ctx.push()
			z3ctx.add(unsatProblem.assertions)
			z3ctx.solve(Valuation())
			z3ctx.pop()
			val core = z3unsatSolver.unsatCore
			dk.solve(ExpressionUtil.and(core), Valuation())
		}
		println("testNoDSL: time spent solving unsat instance: $timeSpentUnsat")
	}

	@Test fun loadZ3withSeq() {
		val timeSpentLoading = measureTimeMillis {
			SolverCompositionDSL.sequentialComposition {
				solver("Z3") {
					identifier = "Z3"
					continuation { _, result, _ ->
						result.stop()
					}
				}
				startWith { "Z3" }
			}
		}
		println("loadZ3withSeq: time spent loading Z3 with SeqDSL-Script: $timeSpentLoading")
	}

	@Test fun loadZ3withoutDSL() {
		val timeSpentLoading = measureTimeMillis {
			ConstraintSolverFactory.createSolver("z3")
		}
		println("loadZ3withoutDSL: time spent loading Z3 without DSL: $timeSpentLoading")
	}

	@Test fun loadZ3withPar() {
		val timeSpentLoading = measureTimeMillis {
			SolverCompositionDSL.parallelComposition {
				solver("Z3") {
					identifier = "Z3"
					ignoredSubset = setOf(ConstraintSolver.Result.ERROR)
				}
				parallelWithLimit(1)
				finalVerdict { results ->
					results.values.firstOrNull() ?: DSLResult(ConstraintSolver.Result.DONT_KNOW, Valuation())
				}
			}
		}
		println("loadZ3withPar: time spent loading Z3 with ParDSL-Script: $timeSpentLoading")
	}
}