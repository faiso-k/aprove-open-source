package aprove.verification.oldframework.Logic;

import aprove.prooftree.Export.Utility.*;

public class ProofFinished implements Implication {

    @Override
    public TruthValue propagate(TruthValue val) {
        return val;
    }

    @Override
    public String export(Export_Util o) {
        return o.equivalent();
    }

    @Override
    public String toString() {
        return "FINISHED";
    }

}
