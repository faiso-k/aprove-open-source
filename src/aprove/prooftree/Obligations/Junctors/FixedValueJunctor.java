package aprove.prooftree.Obligations.Junctors;

import java.util.*;

import aprove.verification.oldframework.Logic.*;

public class FixedValueJunctor implements IJunctor {

    private final TruthValue fixedTruthValue;

    FixedValueJunctor(TruthValue fixedTruthValue) {
        this.fixedTruthValue = fixedTruthValue;
    }

    @Override
    public TruthValue combine(List<? extends TruthValue> truthValues) {
        if (truthValues.size() != 0) {
            throw new IllegalArgumentException("FixedValueJunctor may have no child nodes!");
        }
        return this.fixedTruthValue;
    }

    @Override
    public String getName(int numTruthValues) {
        return this.fixedTruthValue.toString();
    }

}
