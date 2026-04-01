package aprove.verification.complexity.Implications;

import aprove.verification.complexity.TruthValue.*;

public class IdentityComputation implements ComplexityComputation {
    private static final IdentityComputation INSTANCE =
        new IdentityComputation();

    private IdentityComputation() {}

    public static IdentityComputation create() {
        return IdentityComputation.INSTANCE;
    }

    @Override
    public ComplexityValue compute(ComplexityValue input) {
        return input;
    }

    @Override
    public String toString() {
        return "ID";
    }

    @Override
    public ComplexityComputation toAsymptotic() {
        return this;
    }

}