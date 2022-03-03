package instances

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.UNSATCoreSolver
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import solverComposition.entity.CompositionContext
import java.util.*

fun main() {
	partest()
}

fun ConstraintSolver.runSolver() {
	val ctx = createContext()
	var valuation = Valuation()

	if (ctx is UNSATCoreSolver)
		ctx.enableUnsatTracking()

	println("---SAT PROBLEM---")
	ctx.push()
	ctx.add(satProblem.assertions)
	println(ctx.solve(valuation))
	println("valuation: $valuation")
	ctx.pop()

	if (ctx !is CompositionContext)
		satProblem.assertions.evaluateSMT(valuation)

	println()


	valuation = Valuation()
	println("---UNSAT PROBLEM---")
	ctx.push()
	ctx.add(unsatProblem.assertions)
	println(ctx.solve(valuation))
	println("valuation: $valuation")
	ctx.pop()

	if (ctx is UNSATCoreSolver)
		println("core: ${ctx.unsatCore}")

	ctx.dispose()
}

fun seqtest() {
	var timestamp = System.currentTimeMillis()
	val solver = ConstraintSolverFactory.createSolver("seqtest")
	println("Time spent loading solvers: ${System.currentTimeMillis() - timestamp}\n")
	timestamp = System.currentTimeMillis()
	solver.runSolver()
	println("\nTime spent solving: ${System.currentTimeMillis() - timestamp}")
}

fun partest() {
	var timestamp = System.currentTimeMillis()
	val solver = ConstraintSolverFactory.createSolver("partest", Properties().apply {
		setProperty("run", "par")
		setProperty("lim", "1")
	})
	println("Time spent loading solvers: ${System.currentTimeMillis() - timestamp}")
	timestamp = System.currentTimeMillis()
	solver.runSolver()
	println("Time spent solving: ${System.currentTimeMillis() - timestamp}")
}

fun z3Test() {
	var timestamp = System.currentTimeMillis()
	val solver = ConstraintSolverFactory.createSolver("z3")
	println("Time spent loading solvers: ${System.currentTimeMillis() - timestamp}\n")
	timestamp = System.currentTimeMillis()
	solver.runSolver()
	println("\nTime spent solving: ${System.currentTimeMillis() - timestamp}")
}

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

