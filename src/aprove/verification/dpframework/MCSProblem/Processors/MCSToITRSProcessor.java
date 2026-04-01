package aprove.verification.dpframework.MCSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Converts an MCSProblem to an ITRSProblem, thus delegating the proof task to
 * the framework for ITRSs.
 *
 * @author fuhs
 */
public class MCSToITRSProcessor extends MCSProblemProcessor {

    @Override
    public boolean isMCSApplicable(MCSProblem mcs) {
        return true;
    }

    @Override
    protected Result processMCSProblem(MCSProblem mcs, Abortion aborter)
            throws AbortionException {
        Set<HasName> forbiddenNames = new LinkedHashSet<HasName>();
        forbiddenNames.addAll(mcs.getVariables());
        forbiddenNames.addAll(mcs.getFunctionSymbols());
        FreshNameGenerator fng = new FreshNameGenerator(forbiddenNames,
                                        FreshNameGenerator.APPEND_NUMBERS);
        Set<MCRule> mcRules = mcs.getRules();
        Set<GeneralizedRule> itrsRules = new LinkedHashSet<GeneralizedRule>();
        IDPPredefinedMap predefMap = IDPPredefinedMap.DEFAULT_MAP;
        for (MCRule mcRule : mcRules) {
            // convert 1 MC rule to 2 ITRS rules
            mcRule.addITRSRules(fng, predefMap, itrsRules);
        }

        // build Q for innermost rewriting
        QTermSet q = new QTermSet(aprove.verification.dpframework.BasicStructures.CollectionUtils.getLeftHandSides(itrsRules));
        IQTermSet iq = new IQTermSet(q, predefMap);
        ImmutableSet<GeneralizedRule> immutableITRSRules = ImmutableCreator.create(itrsRules);
        ITRSProblem itrs = ITRSProblem.create(immutableITRSRules, predefMap, iq);
        Proof proof = new MCSToITRSProof();
        return ResultFactory.proved(itrs, YNMImplication.EQUIVALENT, proof);
    }

    private static class MCSToITRSProof extends Proof.DefaultProof {

        private MCSToITRSProof() {}

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "We converted the MCS to an equivalent ITRS.";
        }
    }
}
