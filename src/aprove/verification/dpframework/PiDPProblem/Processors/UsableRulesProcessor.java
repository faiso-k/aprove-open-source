package aprove.verification.dpframework.PiDPProblem.Processors;


import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class UsableRulesProcessor extends PiDPProblemProcessor {

    private final boolean beComplete; // only allows application if the application yields a complete method

    public UsableRulesProcessor() {
        this(new Arguments());
    }

    @ParamsViaArgumentObject
    public UsableRulesProcessor(Arguments arguments) {
        this.beComplete = arguments.beComplete;
    }

    @Override
    public boolean isPiDPApplicable(AbstractPiDPProblem pidp) {
        Set<GeneralizedRule> usableRules = pidp.getUsableRules();
        Set<GeneralizedRule> R = pidp.getR();

        // check whether we can gain something
        return (usableRules.size() < R.size());
    }

    @Override
    protected Result processPiDPProblem(AbstractPiDPProblem pidp,
        Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert(this.isApplicable(pidp));
        }

        ImmutableSet<GeneralizedRule> usableRules = pidp.getUsableRules();
        pidp = pidp.getSubProblemWithSmallerR(usableRules);
        Implication implication = YNMImplication.EQUIVALENT;
        Proof proof = new UsableRulesProof();
        return ResultFactory.proved(pidp, implication, proof);

    }

    private static class UsableRulesProof extends Proof.DefaultProof {

        private UsableRulesProof() {
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "For (infinitary) constructor rewriting "+o.cite(Citation.LOPSTR)+" we can delete all non-usable rules from R.";
        }

    }

    public static class Arguments {
        public boolean beComplete = true; // FIXME: never used?
    }

}
