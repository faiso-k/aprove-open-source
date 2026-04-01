package aprove.verification.oldframework.TheoremProverProblem;

import aprove.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.*;

public class TruthToLemmaDatabase implements TruthValueListener {
    public static final TruthToLemmaDatabase INSTANCE = new TruthToLemmaDatabase();

    private TruthToLemmaDatabase() {
        // Singleton.
    }

    @Override
    public void truthValueChanged(TruthValue value, ObligationNode source) {
        if (value != YNM.YES) {
            return;
        }

        BasicObligationNode bOblNode = (BasicObligationNode) source;
        TheoremProverObligation tpObl = (TheoremProverObligation) bOblNode.getBasicObligation();
        LemmaDatabaseFactory.getLemmmaDatabase().insert(
                tpObl.getFormula(), bOblNode);
    }
}
