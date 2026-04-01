package aprove.verification.complexity.Implications;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;

public class LowerBound extends ComplexityImplication {

    private final ComplexityComputation computation;

    private LowerBound(ComplexityComputation c, boolean soundForConcreteBounds) {
        this.computation = c;
        this.soundForConcreteBounds = soundForConcreteBounds;
    }

    public static LowerBound create() {
        return new LowerBound(IdentityComputation.create(), false);
    }

    public static LowerBound create(ComplexityComputation cc) {
        return new LowerBound(cc, false);
    }

    public static LowerBound forConcreteBounds() {
        return new LowerBound(IdentityComputation.create(), true);
    }

    @Override
    protected ComplexityYNM propagateComplexity(ComplexityYNM other) {
        return ComplexityYNM.createLower(
                this.computation.compute(other.getLowerBound()));
    }

    @Override
    public String toString() {
        return (soundForConcreteBounds ? "CONCRETE " : "") + "LOWER BOUND(" + computation + ")";
    }

    @Override
    public String export(Export_Util o) {
        return this.toString();
    }

    @Override
    public ComplexityImplication toAsymptotic() {
        return new LowerBound(computation.toAsymptotic(), false);
    }

}
