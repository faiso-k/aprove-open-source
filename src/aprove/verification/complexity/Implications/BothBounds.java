package aprove.verification.complexity.Implications;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

public class BothBounds extends ComplexityImplication {

    private final ComplexityComputation lowerBound;
    private final ComplexityComputation upperBound;

    private BothBounds(ComplexityComputation lower,
            ComplexityComputation upper,
            boolean soundForConcreteBounds) {
        lowerBound = lower;
        upperBound = upper;
        this.soundForConcreteBounds = soundForConcreteBounds;
    }

    public static BothBounds forConcreteBounds(ComplexityComputation l, ComplexityComputation u) {
        return new BothBounds(l, u, true);
    }

    public static BothBounds forConcreteBounds() {
        return forConcreteBounds(IdentityComputation.create(), IdentityComputation.create());
    }

    public static BothBounds create() {
        return new BothBounds(
                IdentityComputation.create(),
                IdentityComputation.create(),
                false);
    }

    public static BothBounds create(ComplexityComputation lower,
            ComplexityComputation upper) {
        return new BothBounds(lower, upper, false);
    }

    @Override
    protected ComplexityYNM propagateComplexity(ComplexityYNM other) {
        return ComplexityYNM.create(
                this.lowerBound.compute(other.getLowerBound()),
                this.upperBound.compute(other.getUpperBound()));
    }

    @Override
    public String toString() {
        return "BOTH " + (soundForConcreteBounds ? "CONCRETE " : "") + "BOUNDS(" + lowerBound + ", " + upperBound + ")";
    }

    @Override
    public String export(Export_Util o) {
        return this.toString();
    }

    @Override
    public ComplexityImplication toAsymptotic() {
        return new BothBounds(lowerBound.toAsymptotic(), upperBound.toAsymptotic(), false);
    }

}
