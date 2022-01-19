import gov.nasa.jpf.constraints.api.ConstraintSolver
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import solverComposition.dsl.*

internal class ContinuationTest {

	@Test
	fun testUnsatContinueReplace() {
		val actual = (Unsat continueWith "id" andReplaceWith UnsatCore).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.UNSAT,
			continueMode = Continue("id"),
			replaceWithCore = true,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testUnsatContinue() {
		val actual = (Unsat continueWith "id").continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.UNSAT,
			continueMode = Continue("id"),
			replaceWithCore = false,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testUnsatStop() {
		val actual = (Unsat.stop()).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.UNSAT,
			continueMode = Stop,
			replaceWithCore = false,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testSatContinueReplace() {
		val actual = (Sat continueWith "id" andReplaceWith NewModel).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.SAT,
			continueMode = Continue("id"),
			replaceWithCore = false,
			replaceWithNewModel = true,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testSatContinue() {
		val actual = (Sat continueWith "id" andReplaceWith NewModel).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.SAT,
			continueMode = Continue("id"),
			replaceWithCore = false,
			replaceWithNewModel = true,
		)
		assertEquals(expected, actual)
	}

	@Test
	fun testSatStop() {
		val actual = (Sat.stop()).continuation
		val expected = Continuation(
			result = ConstraintSolver.Result.SAT,
			continueMode = Stop,
			replaceWithCore = false,
			replaceWithNewModel = false,
		)
		assertEquals(expected, actual)
	}
}