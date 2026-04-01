package aprove.prooftree.Obligations.Junctors;

import java.util.*;

import aprove.verification.oldframework.Logic.*;

public abstract class AssociativeJunctor implements IJunctor {

    public abstract TruthValue getNeutral();

    public abstract TruthValue combine(TruthValue one, TruthValue other);

    @Override
    public TruthValue combine(List<? extends TruthValue> truthValues) {
        TruthValue result = this.getNeutral();
        for (TruthValue tv : truthValues) {
            result = this.combine(result, tv);
        }
        return result;
    }
}
