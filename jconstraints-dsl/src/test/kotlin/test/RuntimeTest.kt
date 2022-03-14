package test

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.UNSATCoreSolver
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import gov.nasa.jpf.constraints.util.ExpressionUtil
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import solverComposition.dsl.*
import java.math.BigDecimal
import java.math.RoundingMode
import kotlin.math.roundToInt
import kotlin.system.measureNanoTime
import kotlin.system.measureTimeMillis
import kotlin.math.round

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class RuntimeTest {
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

	private val semiPrimeProblem: SMTProblem = SMTLIBParser.parseSMTProgram(
		"""
		(declare-fun A () Int)
		(declare-fun B () Int)
		(assert (>= A 0))      
		(assert (>= B 0))     
		(assert (= (* A B) 932067827)) 
		(assert (not (= 1 A))) 
		(assert (not (= 1 B)))
		(assert (< A B))       
		(check-sat)
		""".trimIndent()
	)

	/**
	 * Creates a SequentialComp that runs Z3 first and MockSolver second.
	 * Continuation of Z3:
	 * Sat -> stop with Sat
	 * Unsat -> continue with MockSolver and replace assertions with core
	 *
	 * Reports the runtime of the Composition when executed on a sat and unsat SMT-Problem to stdout.
	 */
	@Test
	fun measureSeqComp() {
		val runtimeMeasurementsSat = mutableListOf<Long>()
		val runtimeMeasurementsUnsat = mutableListOf<Long>()
		var result: ConstraintSolver.Result?
		val comp = SolverCompositionDSL.sequentialComposition {
			startWith { "Z3" }
			solver("Z3") {
				identifier = "Z3"
				useContext()
				enableUnsatCoreTracking()
				continuation { _, result, _ ->
					when (result) {
						is Sat -> result stopWith ConstraintSolver.Result.SAT
						is Unsat -> result continueWith "mock" andReplaceAssertionsWith UnsatCore
						else -> result stopWith ConstraintSolver.Result.DONT_KNOW
					}
				}
			}
			solver("mock") {
				identifier = "mock"
				continuation { _, result, _ ->
					result.stop()
				}
			}
		}
		val ctx = comp.createContext()
		repeat(15) {
			runtimeMeasurementsSat += measureNanoTime {
				ctx.push()
				ctx.add(satProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
			}
			assertEquals(ConstraintSolver.Result.SAT, result)
			runtimeMeasurementsUnsat += measureNanoTime {
				ctx.push()
				ctx.add(unsatProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
			}
			assertEquals(ConstraintSolver.Result.DONT_KNOW, result)
		}
		println("${this::measureSeqComp.name}: Time spent solving SAT instance: $runtimeMeasurementsSat")
		println("${this::measureSeqComp.name}: Copy for latex: ${runtimeMeasurementsSat.toLatexFormat()} % average: ${runtimeMeasurementsSat.sum() / runtimeMeasurementsSat.size}")
		println("${this::measureSeqComp.name}: Time spent solving UNSAT instance: $runtimeMeasurementsUnsat")
		println("${this::measureSeqComp.name}: Copy for latex: ${runtimeMeasurementsUnsat.toLatexFormat()} % average: ${runtimeMeasurementsUnsat.sum() / runtimeMeasurementsUnsat.size}")
	}

	private fun List<Long>.toLatexFormat(isNano: Boolean = true)  = this
		.mapIndexed(Int::to)
		.joinToString("") {
			"(${
				it.first + 1
			},${
				BigDecimal(it.second / if (isNano) 1000000.0 else 1.0).setScale(2, RoundingMode.HALF_EVEN)
			})"
		}

	/**
	 * Manual Implementation of the Composition in [measureSeqComp].
	 */
	@Test
	fun measureSeqManualReuseCTX() {
		val runtimeMeasurementsSat = mutableListOf<Long>()
		val runtimeMeasurementsUnsat = mutableListOf<Long>()
		var result: ConstraintSolver.Result?
		val z3 = ConstraintSolverFactory.createSolver("z3")
		val mock = ConstraintSolverFactory.createSolver("mock")
		val ctx = z3.createContext()
		ctx as UNSATCoreSolver
		ctx.enableUnsatTracking()
		repeat(15) {
			runtimeMeasurementsSat += measureNanoTime {
				ctx.push()
				ctx.add(satProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
			}
			assertEquals(ConstraintSolver.Result.SAT, result)
			runtimeMeasurementsUnsat += measureNanoTime {
				ctx.push()
				ctx.add(unsatProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
				val core = ctx.unsatCore
				mock.solve(ExpressionUtil.and(core), Valuation())
			}
			assertEquals(ConstraintSolver.Result.UNSAT, result)
		}
		ctx.dispose()
		println("${this::measureSeqManualReuseCTX.name}: Time spent solving SAT instance without replacing ctx: $runtimeMeasurementsSat")
		println("${this::measureSeqManualReuseCTX.name}: Copy for latex: ${runtimeMeasurementsSat.toLatexFormat()} % average: ${runtimeMeasurementsSat.sum() / runtimeMeasurementsSat.size}")
		println("${this::measureSeqManualReuseCTX.name}: Time spent solving UNSAT instance without replacing ctx: $runtimeMeasurementsUnsat")
		println("${this::measureSeqManualReuseCTX.name}: Copy for latex: ${runtimeMeasurementsUnsat.toLatexFormat()} % average: ${runtimeMeasurementsUnsat.sum() / runtimeMeasurementsUnsat.size}")
	}

	/**
	 * Manual Implementation of the Composition in [measureSeqComp].
	 * A New Context is created for every solve call.
	 */
	@Test
	fun measureSeqManualNewCTX() {
		val runtimeMeasurementsSat = mutableListOf<Long>()
		val runtimeMeasurementsUnsat = mutableListOf<Long>()
		var result: ConstraintSolver.Result?
		val z3 = ConstraintSolverFactory.createSolver("z3")
		val mock = ConstraintSolverFactory.createSolver("mock")
		repeat(15) {
			runtimeMeasurementsSat += measureNanoTime {
				val ctx = z3.createContext()
				ctx as UNSATCoreSolver
				ctx.enableUnsatTracking()
				ctx.push()
				ctx.add(satProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
				ctx.dispose()
			}
			assertEquals(ConstraintSolver.Result.SAT, result)
			runtimeMeasurementsUnsat += measureNanoTime {
				val ctx = z3.createContext()
				ctx as UNSATCoreSolver
				ctx.enableUnsatTracking()
				ctx.push()
				ctx.add(unsatProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
				val core = ctx.unsatCore
				mock.solve(ExpressionUtil.and(core), Valuation())
				ctx.dispose()
			}
			assertEquals(ConstraintSolver.Result.UNSAT, result)
		}
		println("${this::measureSeqManualNewCTX.name}: Time spent solving SAT instance with replacing ctx: $runtimeMeasurementsSat")
		println("${this::measureSeqManualNewCTX.name}: Copy for latex: ${runtimeMeasurementsSat.toLatexFormat()} % average: ${runtimeMeasurementsSat.sum() / runtimeMeasurementsSat.size}")
		println("${this::measureSeqManualNewCTX.name}: Time spent solving UNSAT instance with replacing ctx: $runtimeMeasurementsUnsat")
		println("${this::measureSeqManualNewCTX.name}: Copy for latex: ${runtimeMeasurementsUnsat.toLatexFormat()} % average: ${runtimeMeasurementsUnsat.sum() / runtimeMeasurementsUnsat.size}")
	}

	/**
	 * Measures the runtime of a SMT-Problem describing the factorization of the semi-prime 932067827.
	 * Runtime is Measured for a ParallelComposition consisting of 5 Z3 instances in parallel
	 * and for manually solving the same Problem by 5 Z3 instances in sequence.
	 */
	@Test
	fun measureParComp() {
		val runtimeMeasurements = mutableListOf<Long>()
		val comp = SolverCompositionDSL.parallelComposition {
			parallel()
			repeat(5) {
				solver("Z3") {
					identifier = "Z3$it"
					useContext()
				}
			}
			finalVerdict {
				it.values.first()
			}
		}
		val ctx = comp.createContext()
		var result: ConstraintSolver.Result?
		repeat(15) {
			println("stating $it")
			runtimeMeasurements += measureNanoTime {
				ctx.push()
				ctx.add(semiPrimeProblem.assertions)
				result = ctx.solve(Valuation())
				ctx.pop()
				assertEquals(ConstraintSolver.Result.SAT, result)
			}
			println("last: ${runtimeMeasurements.last() / 1000000000}")
		}
		println("${this::measureParComp.name}: Time spent solving with ParallelComposition: $runtimeMeasurements")
		println("${this::measureParComp.name}: copy for latex: ${runtimeMeasurements.toLatexFormat()} % average: ${runtimeMeasurements.sum() / runtimeMeasurements.size}}")
		runtimeMeasurements.clear()
		val z3 = ConstraintSolverFactory.createSolver("z3")
		repeat(15) {
			println("stating $it")
			runtimeMeasurements += measureNanoTime {
				val z3ctx = z3.createContext()
				z3ctx.add(semiPrimeProblem.assertions)
				result = z3ctx.solve(Valuation())
				z3ctx.dispose()
				assertEquals(ConstraintSolver.Result.SAT, result)
			}
		}
		println("${this::measureParComp.name}: Time spent solving with Z3: $runtimeMeasurements")
		println("${this::measureParComp.name}: copy for latex: ${runtimeMeasurements.toLatexFormat()} % average: ${runtimeMeasurements.sum() / runtimeMeasurements.size}}")
	}

	/**
	 * Runs 10 mocks in parallel with a limit of 7.
	 * The runtimes of the mocks are as follows:
	 * mock0 = 0ms
	 * mock1 = 100ms
	 * mock2 = 200ms
	 * etc.
	 *
	 * So the expected runtime is ~600ms.
	 */
	@Test
	fun measureMockParComp() {
		val runtimeMeasurements = mutableListOf<Long>()
		val comp = SolverCompositionDSL.parallelComposition {
			repeat(1000) {
				solver("mock") {
					identifier = "mock$it"
					configuration["timeout"] = "${it}00"
				}
			}
			parallelWithLimit(7)
			finalVerdict { results ->
				results.values.first()
			}
		}
		val assertion = satProblem.allAssertionsAsConjunction
		repeat(15) {
			runtimeMeasurements += measureTimeMillis {
				comp.solve(assertion, Valuation())
			}
		}
		println("${this::measureParComp.name}: Time spent solving with ParallelComposition: $runtimeMeasurements")
		println("${this::measureParComp.name}: copy for latex: ${runtimeMeasurements.toLatexFormat(false)} % average: ${runtimeMeasurements.sum() / runtimeMeasurements.size}")
	}

	@Test
	fun measureLoadSeq() {
		val runtimeMeasurements = mutableListOf<Long>()
		repeat(15) {
			runtimeMeasurements += measureNanoTime {
				ConstraintSolverFactory.createSolver("test seq prov")
			}
		}
		println("${this::measureLoadSeq.name}: Time spent loading: $runtimeMeasurements")
		println("${this::measureLoadSeq.name}: copy for latex: ${runtimeMeasurements.toLatexFormat()} % average: ${runtimeMeasurements.sum() / runtimeMeasurements.size}")
	}

	@Test
	fun measureLoadPar() {
		val runtimeMeasurements = mutableListOf<Long>()
		repeat(15) {
			runtimeMeasurements += measureNanoTime {
				ConstraintSolverFactory.createSolver("test par prov")
			}
		}
		println("${this::measureLoadPar.name}: Time spent loading: $runtimeMeasurements")
		println("${this::measureLoadPar.name}: copy for latex: ${runtimeMeasurements.toLatexFormat()} % average: ${runtimeMeasurements.sum() / runtimeMeasurements.size}")
	}

	@Test
	fun measureLoadMock() {
		val runtimeMeasurements = mutableListOf<Long>()
		repeat(15) {
			runtimeMeasurements += measureNanoTime {
				ConstraintSolverFactory.createSolver("mock")
			}
		}
		println("${this::measureLoadMock.name}: Time spent loading: $runtimeMeasurements")
		println("${this::measureLoadMock.name}: copy for latex: ${runtimeMeasurements.toLatexFormat()} % average: ${runtimeMeasurements.sum() / runtimeMeasurements.size}")
	}
}