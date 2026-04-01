/**
 *
 */
package aprove.verification.complexity.Implications;

import aprove.verification.complexity.TruthValue.*;

public class SumComputation implements ComplexityComputation {

    private final ComplexityValue summand;

    public SumComputation(ComplexityValue summand) {
        this.summand = summand;
    }

    @Override
    public ComplexityValue compute(ComplexityValue other) {
        return summand.add(other);
    }

    @Override
    public String toString() {
        return "ADD(" + this.summand + ")";
    }

    @Override
    public ComplexityComputation toAsymptotic() {
        if (summand.isConstant()) {
            return IdentityComputation.create();
        } else {
            return new SumComputation(summand.discardConcreteValue());
        }
    }

}