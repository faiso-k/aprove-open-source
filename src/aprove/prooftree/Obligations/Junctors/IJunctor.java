package aprove.prooftree.Obligations.Junctors;

import java.util.*;

import aprove.verification.oldframework.Logic.*;

public interface IJunctor {

    public abstract TruthValue combine(List<? extends TruthValue> truthValues);

    /**
     * @return a short describing name.
     *
     * @param numTruthValues
     *            Number of truth values to be combined with this junctor.
     */
    public abstract String getName(int numTruthValues);

}