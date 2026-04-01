package aprove.prooftree.Obligations.Junctors;

import aprove.verification.oldframework.Logic.*;

public class OrJunctor extends AssociativeJunctor {

    OrJunctor() {}

    @Override
    public TruthValue getNeutral() {
        return YNM.NO;
    }

    @Override
    public TruthValue combine(TruthValue one, TruthValue other) {
        return one.or(other);
    }

    @Override
    public String getName(int numTruthValues){
        return numTruthValues == 0 ? "FALSE" : "OR";
    }

}
