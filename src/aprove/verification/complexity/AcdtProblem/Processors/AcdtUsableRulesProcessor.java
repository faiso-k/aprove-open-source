package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class AcdtUsableRulesProcessor extends AcdtProblemProcessor {

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        UsableRulesCalculator ucalc = cdtProblem.getURCalc();
        Set<Rule> usableRules = new LinkedHashSet<Rule>();
        for (Acdt cdt : cdtProblem.getTuples()) {
            usableRules.addAll(IcapAlgorithm.renumberedRules(
                    Collections.singleton(cdt.getBaseRule())));
            usableRules.addAll(ucalc.estimateUsableRules(cdt.getRule()));
        }

        ImmutableSet<Rule> oldRules = cdtProblem.getR();
        if (usableRules.equals(oldRules)) {
            return ResultFactory.unsuccessful("All rules are usable");
        } else {
            Set<Rule> removedRules = new LinkedHashSet<Rule>(oldRules);
            removedRules.removeAll(usableRules);
            return ResultFactory.proved(
                    cdtProblem.createSubproblem(usableRules),
                    BothBounds.create(),
                    new CdtUsableRulesProof(removedRules));
        }
    }

    public class CdtUsableRulesProof extends DefaultProof {

        private final Set<Rule> removedRules;

        public CdtUsableRulesProof(Set<Rule> removedRules) {
            this.removedRules = removedRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("The following rules are not usable and were removed:")
                    + o.set(this.removedRules, Export_Util.RULES);
        }

    }

}
