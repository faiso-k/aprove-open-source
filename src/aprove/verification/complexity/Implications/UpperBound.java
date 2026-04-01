package aprove.verification.complexity.Implications;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

public class UpperBound extends ComplexityImplication {

    private final ComplexityComputation computation;

    private UpperBound(ComplexityComputation c, boolean soundForConcreteBounds) {
        computation = c;
        this.soundForConcreteBounds = soundForConcreteBounds;
    }

    public static UpperBound create() {
        return new UpperBound(IdentityComputation.create(), false);
    }

    public static UpperBound forConcreteBounds() {
        return new UpperBound(IdentityComputation.create(), true);
    }

    public static UpperBound create(ComplexityComputation cc) {
        return new UpperBound(cc, false);
    }

    @Override
    protected ComplexityYNM propagateComplexity(ComplexityYNM other) {
        return ComplexityYNM.createUpper(
                this.computation.compute(other.getUpperBound()));
    }

    @Override
    public String toString() {
        return (soundForConcreteBounds ? "CONCRETE " : "") + "UPPER BOUND(" + computation + ")";
    }

    @Override
    public String export(Export_Util o) {
        return this.toString();
    }

    @Override
    public ComplexityImplication toAsymptotic() {
        return new UpperBound(computation.toAsymptotic(), false);
    }

}
