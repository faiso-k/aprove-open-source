package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

public class CdtUsableRulesProcessor extends CdtProblemProcessor {

    @Override
    protected boolean isCdtApplicable(final CdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(final CdtProblem cdtProblem, final Abortion aborter)
            throws AbortionException {
        final UsableRulesCalculator ucalc = cdtProblem.getURCalc();
        final Set<Rule> usableRules = new LinkedHashSet<Rule>();
        for (final Cdt cdt : cdtProblem.getTuples()) {
            usableRules.addAll(ucalc.estimateUsableRules(cdt.getRule()));
        }

        final ImmutableSet<Rule> oldRules = cdtProblem.getR();
        if (usableRules.equals(oldRules)) {
            return ResultFactory.unsuccessful("All rules are usable");
        } else {
            final Set<Rule> removedRules = new LinkedHashSet<Rule>(oldRules);
            removedRules.removeAll(usableRules);
            return ResultFactory.proved(
                    cdtProblem.createSubproblem(usableRules),
                    BothBounds.create(),
                    new CdtUsableRulesProof(removedRules));
        }
    }

    public class CdtUsableRulesProof extends CpxProof {

        private final Set<Rule> removedRules;

        public CdtUsableRulesProof(final Set<Rule> removedRules) {
            this.removedRules = removedRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.escape("The following rules are not usable and were removed:")
                    + o.set(this.removedRules, Export_Util.RULES);
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            final Element res = CPFTag.USABLE_RULES.create(doc,
                CPFTag.NON_USABLE_RULES.create(doc,
                    CPFTag.rules(doc, xmlMetaData, this.removedRules)),
                childrenProofs[0]);
            return this.positiveTag().create(doc, res);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

}
