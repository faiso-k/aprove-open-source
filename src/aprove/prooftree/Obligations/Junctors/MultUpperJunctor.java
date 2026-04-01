package aprove.prooftree.Obligations.Junctors;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

/*
 * Junctor which computes the maximum of the upper bound
 * (and sets the lower bound to O(1)
 */
public class MultUpperJunctor extends AssociativeJunctor {

    MultUpperJunctor() {}

    @Override
    public TruthValue getNeutral() {
        return ComplexityYNM.CONSTANT;
    }

    @Override
    public TruthValue combine(TruthValue one, TruthValue other) {
        return one.mult(other);
    }

    @Override
    public String getName(int numTruthValues){
        return numTruthValues == 0 ? "O(1)" : "MULT";
    }

}
