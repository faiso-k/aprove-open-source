package aprove.prooftree.Obligations.Junctors;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

/*
 * Junctor which computes the best complexity bound.
 */
public class BestComplexityJunctor extends AssociativeJunctor {

    BestComplexityJunctor() {}

    @Override
    public TruthValue getNeutral() {
        return ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.infinite());
    }

    @Override
    public TruthValue combine(TruthValue one, TruthValue other) {
        return one.or(other);
    }

    @Override
    public String getName(int numTruthValues){
        return numTruthValues == 0 ? this.getNeutral().toString() : "BEST";
    }

}
