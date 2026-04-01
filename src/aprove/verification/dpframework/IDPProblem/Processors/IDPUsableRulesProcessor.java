package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IUsableRulesEstimation.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class IDPUsableRulesProcessor extends IDPProcessor {

    /**
     * only allows application if the application yields a complete method
     */
    private final IUsableRulesEstimation.Estimations estimation;

    @ParamsViaArgumentObject
    public IDPUsableRulesProcessor(final Arguments arguments) {
        this(arguments.estimation);
    }

    public IDPUsableRulesProcessor(final Estimations estimation) {
        this.estimation = estimation;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return idp.getRuleAnalysis().isNfQSubsetEqNfR();
    }

    @Override
    protected Result processIDPProblem(final IDPProblem idp, final Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert (this.isApplicable(idp));
        }

        final Set<GeneralizedRule> usableRules =
            new LinkedHashSet<GeneralizedRule>(
                    idp.getRuleAnalysis().getUseableRules(this.estimation).getActive().keySet()
            );
        final Iterator<GeneralizedRule> iter = usableRules.iterator();
        final IDPPredefinedMap preDefined = idp.getRuleAnalysis().getPreDefinedMap();
        while (iter.hasNext()) {
            if (preDefined.isPredefined(iter.next().getLeft().getRootSymbol())) {
                iter.remove();
            }
        }
        if (idp.getR().equals(usableRules)) {
            return ResultFactory.unsuccessful();
        }
        final RuleAnalysis<GeneralizedRule> newRules =
            new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(usableRules),
                idp.getRuleAnalysis().getPreDefinedMap());

        final Result result =
            ResultFactory.proved(idp.change(null, newRules, null, null, this), YNMImplication.EQUIVALENT,
                new UsableRulesProof(null, true));
        return result;

    }

    private static class UsableRulesProof extends Proof.DefaultProof {

        private final Set<GeneralizedRule> ceRules;
        private final boolean innermost;

        private UsableRulesProof(final Set<GeneralizedRule> ceRules, final boolean innermost) {
            this.ceRules = ceRules;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res;
            String afterRes = null;
            if (this.innermost) {
                res =
                    "As all Q-normal forms are R-normal forms we are in the innermost case. "
                        + "Hence, by the usable rules processor " + o.cite(Citation.LPAR04)
                        + " we can delete all non-usable rules " + o.cite(Citation.FROCOS05) + " from R.";
            } else {
                if (this.ceRules != null) {
                    res =
                        "We use the Ce-Transformation " + o.cite(Citation.JAR06) + " to delete all non-usable rules "
                            + o.cite(Citation.FROCOS05) + " from R, but "
                            + "we lose minimality and add the following 2 Ce-rules:";
                    afterRes = o.set(this.ceRules, Export_Util.RULES);
                } else {
                    res =
                        "We can use the usable rules and reduction pair processor " + o.cite(Citation.LPAR04)
                            + " with the Ce-compatible extension of the "
                            + "polynomial order that maps every function symbol to the sum of its arguments. "
                            + "Then, we can delete all non-usable rules " + o.cite(Citation.FROCOS05) + " from R.";
                }
            }
            return o.export(res) + (afterRes == null ? "" : afterRes);
        }

    }

    public static class Arguments {
        public IUsableRulesEstimation.Estimations estimation = null;
    }
}
