package aprove.verification.complexity.Implications;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

public abstract class ComplexityImplication implements Implication {

    boolean soundForConcreteBounds;

    @Override
    public final TruthValue propagate(TruthValue other) throws IncompatibleTruthValueException {
        if (other == YNM.MAYBE) {
            other = ComplexityYNM.MAYBE;
        } else if (!(other instanceof ComplexityYNM)) {
            throw new IncompatibleTruthValueException("Cannot propagate non-ComplexityYNM TruthValue: " + other);
        }
        ComplexityYNM res = propagateComplexity((ComplexityYNM) other);
        return soundForConcreteBounds ? res : res.discardConcreteValues();
    }

    public abstract ComplexityImplication toAsymptotic();

    protected abstract ComplexityYNM propagateComplexity(ComplexityYNM other);

}
