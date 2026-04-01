package aprove.verification.complexity.LowerBounds.BasicStructures;

import aprove.verification.dpframework.BasicStructures.*;


public class InductionHypothesis extends AbstractRule {

    public InductionHypothesis(TRSFunctionApplication lhs, TRSTerm rhs) {
        super(lhs, rhs);
    }

    @Override
    public Complexity getComplexity() {
        return Complexity.UNKNOWN;
    }

    @Override
    InductionHypothesis cloneWith(TRSFunctionApplication lhs, TRSTerm rhs) {
        return new InductionHypothesis(lhs, rhs);
    }

    @Override
    public String getIndex() {
        return "IH";
    }

}
