package aprove.prooftree.Obligations.Junctors;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Junctor which computes the minimum of the upper bounds
 * (with infinity as neutral element).
 */
public class MinUpperJunctor extends AssociativeJunctor {

    MinUpperJunctor() {}

    @Override
    public TruthValue getNeutral() {
        return ComplexityYNM.INFINITE;
    }

    @Override
    public TruthValue combine(TruthValue one, TruthValue other) {
        return one.or(other);
    }

    @Override
    public String getName(int numTruthValues){
        return numTruthValues == 0 ? "INF" : "MIN";
    }

}
