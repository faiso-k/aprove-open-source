package aprove.verification.oldframework.Logic;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;

/**
 * Returns a given complexity if the system below is terminating, else
 * {@link ComplexityYNM}.MAYBE.
 */
public class ComplexityIfTerminatingImplication implements Implication {

    private final TruthValue tv;

    private ComplexityIfTerminatingImplication(TruthValue tv) {
        this.tv = tv;
    }

    public static ComplexityIfTerminatingImplication create(TruthValue tv) {
        return new ComplexityIfTerminatingImplication(tv);
    }

    @Override
    public final TruthValue propagate(TruthValue other) {
        if (other.fallbackToYNM() == YNM.YES) {
            return this.tv;
        } else {
            return ComplexityYNM.MAYBE;
        }
    }

    @Override
    public String toString() {
        return "ComplexityIfTerminatingImplication(" + this.tv + ")";
    }

    @Override
    public String export(Export_Util o) {
        return this.toString();
    }
}
