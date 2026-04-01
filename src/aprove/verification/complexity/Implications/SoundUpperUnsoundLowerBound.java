package aprove.verification.complexity.Implications;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

public class SoundUpperUnsoundLowerBound extends ComplexityImplication {

    private final ComplexityComputation lowerBound;
    private final ComplexityComputation upperBound;

    private SoundUpperUnsoundLowerBound(ComplexityComputation lower,
            ComplexityComputation upper,
            boolean soundForConcreteBounds) {
        lowerBound = lower;
        upperBound = upper;
        this.soundForConcreteBounds = soundForConcreteBounds;
    }

    public static SoundUpperUnsoundLowerBound forConcreteBounds(ComplexityComputation l, ComplexityComputation u) {
        return new SoundUpperUnsoundLowerBound(l, u, true);
    }

    public static SoundUpperUnsoundLowerBound forConcreteBounds() {
        return forConcreteBounds(IdentityComputation.create(), IdentityComputation.create());
    }

    public static SoundUpperUnsoundLowerBound create() {
        return new SoundUpperUnsoundLowerBound(
                IdentityComputation.create(),
                IdentityComputation.create(),
                false);
    }

    public static SoundUpperUnsoundLowerBound create(ComplexityComputation lower,
            ComplexityComputation upper) {
        return new SoundUpperUnsoundLowerBound(lower, upper, false);
    }

    @Override
    protected ComplexityYNM propagateComplexity(ComplexityYNM other) {
        return ComplexityYNM.create(
                this.lowerBound.compute(other.getLowerBound()),
                this.upperBound.compute(other.getUpperBound()));
    }

    @Override
    public String toString() {
        return "UNSOUND " + (soundForConcreteBounds ? "CONCRETE " : "") + "LOWER BOUND(" + lowerBound + ")" +
                "SOUND " + (soundForConcreteBounds ? "CONCRETE " : "") + "UPPER BOUND(" + upperBound + ")";
    }

    @Override
    public String export(Export_Util o) {
        return this.toString();
    }

    @Override
    public ComplexityImplication toAsymptotic() {
        return new SoundUpperUnsoundLowerBound(lowerBound.toAsymptotic(), upperBound.toAsymptotic(), false);
    }

}
