package aprove.verification.oldframework.Logic;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;

/**
 * Returns the complexity of the system below, if it is at most polynomial.
 * Otherwise it collapses complexity results to MAYBE/FINITE/INFINITE.
 */
public class ComplexityIfPolyImplication implements Implication {

    public static ComplexityIfPolyImplication create() {
        return new ComplexityIfPolyImplication();
    }

    @Override
    public final TruthValue propagate(TruthValue other) {
        if (other instanceof ComplexityYNM) {
            ComplexityYNM cynm = (ComplexityYNM)other;
            ComplexityValue lowerBound = cynm.getLowerBound();
            ComplexityValue upperBound = cynm.getUpperBound();
            if (upperBound.compareTo(ComplexityValue.polynomial()) <= 0) {
                return other;
            } else {
                if (upperBound.compareTo(ComplexityValue.finite()) <= 0){
                    return ComplexityYNM.create(lowerBound, ComplexityValue.finite());
                } else {
                    return ComplexityYNM.createLower(lowerBound);
                }
            }
        } else if (other.fallbackToYNM() == YNM.YES) {
            return ComplexityYNM.createUpper(ComplexityValue.finite());
        } else {
            return ComplexityYNM.MAYBE;
        }
    }

    @Override
    public String toString() {
        return "ComplexityIfPolyImplication";
    }

    @Override
    public String export(Export_Util o) {
        return this.toString();
    }
}
