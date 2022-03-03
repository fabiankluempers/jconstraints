package test

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.UNSATCoreSolver
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import gov.nasa.jpf.constraints.util.ExpressionUtil
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import solverComposition.dsl.Sat
import solverComposition.dsl.SolverCompositionDSL
import solverComposition.dsl.Unsat
import solverComposition.dsl.UnsatCore
import solverComposition.entity.DSLResult
import kotlin.system.measureTimeMillis

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SeqRuntimeTest {

	private val unsatProblem: SMTProblem = SMTLIBParser.parseSMTProgram(
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

	private val satProblem: SMTProblem = SMTLIBParser.parseSMTProgram(
		"""
		(declare-fun A () Int)
		(declare-fun B () Int)
		(assert (= A B))
		(assert (= A 5))
		""".trimIndent()
	)

	/**
	 * loads all the solvers used in this testsuite once, to eliminate the initial load times of
	 * [ConstraintSolverFactory.createSolver].
	 *
	 * Also executes create context and some solving on Z3 because somehow the first
	 * calls to solve lead to longer response times than consecutive ones.
	 *
	 * This leads to better comparability of the measured runtimes in this testsuite.
	 */
	@BeforeAll fun initialLoad() {
		val z3 = ConstraintSolverFactory.createSolver("z3").createContext()
		z3 as UNSATCoreSolver
		ConstraintSolverFactory.createSolver("dontKnow")
		ConstraintSolverFactory.createSolver("mock")
		z3.push()
		z3.add(satProblem.assertions)
		z3.solve(Valuation())
		z3.pop()
		z3.enableUnsatTracking()
		z3.push()
		z3.add(unsatProblem.assertions)
		z3.solve(Valuation())
		z3.unsatCore
		z3.pop()
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

	/**
	 * Creates a SequentialComposition with 10.000 mock solvers via [genSeqMockComp].
	 * Reports the measured runtime for instantiating and solving to stdout.
	 */
	@DisplayName("Report Runtime of a SequentialComposition with 10k mock Solvers")
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

	/**
	 * Creates a ParallelComposition with 10.000 mock solvers via [genParMockComp].
	 * Reports the measured runtime for instantiating and solving to stdout.
	 */
	@DisplayName("Report Runtime of a ParallelComposition with 10k mock Solvers")
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

	/**
	 * Creates a SequentialComp that runs Z3 first and DontKnow second.
	 * Continuation of Z3:
	 * Sat -> stop with Sat
	 * Unsat -> continue with DontKnowSolver and replace assertions with core
	 *
	 * Reports the runtime of the Composition when executed on a sat and unsat SMT-Problem to stdout.
	 */
	@DisplayName("Report Runtime of a SequentialComposition using the Z3 Solver")
	@Test fun testZ3inSeq() {
		var result : ConstraintSolver.Result?
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
			result = ctx.solve(Valuation())
			ctx.pop()
		}
		assertEquals(ConstraintSolver.Result.SAT, result)
		println("testZ3inSeq: time spent solving sat instance: $timeSpentSat")
		val timeSpentUnsat = measureTimeMillis {
			ctx.push()
			ctx.add(unsatProblem.assertions)
			result = ctx.solve(Valuation())
			ctx.pop()
		}
		assertEquals(ConstraintSolver.Result.DONT_KNOW, result)
		println("testZ3inSeq: time spent solving unsat instance: $timeSpentUnsat")
	}

	/**
	 * Manual Implementation of the Composition in [testZ3inSeq].
	 */
	@DisplayName("Report Runtime of manual Implementation of a metasolving-strategy")
	@Test fun testNoDSL() {
		var result : ConstraintSolver.Result?
		val z3 = ConstraintSolverFactory.createSolver("z3")
		val dk = ConstraintSolverFactory.createSolver("z3")
		val ctx = z3.createContext()
		ctx as UNSATCoreSolver
		ctx.enableUnsatTracking()
		val timeSpentSat = measureTimeMillis {
			ctx.push()
			ctx.add(satProblem.assertions)
			result = ctx.solve(Valuation())
			ctx.pop()
			//dk.solve(satProblem.allAssertionsAsConjunction, Valuation())
		}
		assertEquals(ConstraintSolver.Result.SAT, result)
		println("testNoDSL: time spent solving sat instance: $timeSpentSat")
		val timeSpentUnsat = measureTimeMillis {
			ctx.push()
			ctx.add(unsatProblem.assertions)
			result = ctx.solve(Valuation())
			ctx.pop()
			val core = ctx.unsatCore
			dk.solve(ExpressionUtil.and(core), Valuation())
		}
		assertEquals(ConstraintSolver.Result.UNSAT, result)
		println("testNoDSL: time spent solving unsat instance: $timeSpentUnsat")
	}

	@DisplayName("Report Runtime of loading Z3 in a SequentialComposition")
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

	@DisplayName("Report Runtime of loading Z3.")
	@Test fun loadZ3withoutDSL() {
		val timeSpentLoading = measureTimeMillis {
			ConstraintSolverFactory.createSolver("z3")
		}
		println("loadZ3withoutDSL: time spent loading Z3 without DSL: $timeSpentLoading")
	}

	@DisplayName("Report Runtime of loading Z3 in a ParallelComposition")
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

	@DisplayName("Report runtime of 20 Z3 instances")
	@Test fun test20z3parallel() {
		val comp = SolverCompositionDSL.parallelComposition {
			parallel()
			repeat(20) {
				solver("Z3") {
					identifier = "Z3$it"
				}
			}
			finalVerdict {
				it.values.first()
			}
		}
		var assertion = satProblem.allAssertionsAsConjunction
		var result : ConstraintSolver.Result?
		var timeSpentSolving = measureTimeMillis {
			result = comp.solve(assertion, Valuation())
		}
		assertEquals(ConstraintSolver.Result.SAT, result)
		println("test10z3parallel: time spent solving sat instance: $timeSpentSolving")
		assertion = unsatProblem.allAssertionsAsConjunction
		timeSpentSolving = measureTimeMillis {
			result = comp.solve(assertion, Valuation())
		}
		assertEquals(ConstraintSolver.Result.UNSAT, result)
		println("test10z3parallel: time spent solving unsat instance: $timeSpentSolving")
		assertion = satProblem.allAssertionsAsConjunction
		val z3s = mutableListOf<ConstraintSolver>()
		repeat(20) { z3s.add(ConstraintSolverFactory.createSolver("Z3")) }
		timeSpentSolving = measureTimeMillis {
			for (z3 in z3s) {
				z3.solve(assertion, Valuation())
			}
		}
		println("test10z3parallel: time spent manually and sequentially solving sat instance: $timeSpentSolving")
		assertion = unsatProblem.allAssertionsAsConjunction
		timeSpentSolving = measureTimeMillis {
			for (z3 in z3s) {
				z3.solve(assertion, Valuation())
			}
		}
		println("test10z3parallel: time spent manually and sequentially solving unsat instance: $timeSpentSolving")
	}
}
