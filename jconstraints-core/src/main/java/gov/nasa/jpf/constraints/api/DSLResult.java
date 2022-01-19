package gov.nasa.jpf.constraints.api;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;

/**
 * Used as a return object for {@link ConstraintSolver} dslSolve method.
 */
public class DSLResult {
    private final ConstraintSolver.Result result;
    private final Valuation valuation;

    public DSLResult(ConstraintSolver.Result result, Valuation valuation) {
        this.result = result;
        this.valuation = valuation;
    }


    public ConstraintSolver.Result getResult() {
        return result;
    }

    public Valuation getValuation() {
        return valuation;
    }
}
