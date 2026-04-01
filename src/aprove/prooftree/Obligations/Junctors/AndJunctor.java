package aprove.prooftree.Obligations.Junctors;

import aprove.verification.oldframework.Logic.*;

public class AndJunctor extends AssociativeJunctor {

    AndJunctor() {}

    @Override
    public TruthValue getNeutral() {
        return YNM.YES;
    }

    @Override
    public TruthValue combine(TruthValue one, TruthValue other) {
        return one.and(other);
    }

    @Override
    public String getName(int numTruthValues){
        return numTruthValues == 0 ? "TRUE" : "AND";
    }

}
