package aprove.verification.oldframework.IRSwT.Processors.ExportProcessors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Turns an IRSwT into an IDP in a quite simple way:
 * If R' is the given integer rewrite system, then we set
 * P = R', R = E, Q = E [here E = the empty set!] to define the IDP (Q,P,R).
 * @author Matthias Hoelzel
 */
public class IRSwTToIDPProcessor extends Processor.ProcessorSkeleton {
    /** Constructor! */
    public IRSwTToIDPProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl != null && obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded());
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSwTProblem intTRS = (IRSwTProblem) obl;

        // We never don't want no Q:
        final List<TRSFunctionApplication> qTerms = new LinkedList<>();
        final QTermSet q = new QTermSet(qTerms);
        final IQTermSet iq = new IQTermSet(q, IDPPredefinedMap.DEFAULT_MAP);
        aborter.checkAbortion();

        // Use the odd transformation to move conditions to another place.
        final LinkedHashSet<IGeneralizedRule> filteredRules = new LinkedHashSet<>();
        RemoveFreeVarsFromCond freeVarFilter = new RemoveFreeVarsFromCond(false);
        for (final IGeneralizedRule rule : intTRS.getRules()) {
            filteredRules.add(freeVarFilter.removeFreeVarsFromCond(rule));
        }
        final Set<GeneralizedRule> generalizedRules = IGeneralizedRule.removeConditions(filteredRules, true);

        // Put everything into an IDP analysis to obtain a IDP problem:
        final IDPRuleAnalysis idpAnalysis =
            new IDPRuleAnalysis(
                ImmutableCreator.create(new LinkedHashSet<GeneralizedRule>(0)),
                ImmutableCreator.create(generalizedRules),
                iq,
                null);
        final IDPProblem idpProblem = IDPProblem.create(idpAnalysis, false, aborter);

        return ResultFactory.proved(idpProblem, YNMImplication.SOUND, new IRSwTToIDPProof());
    }

    /**
     * A truly pestilent proof!
     * @author Matthias Hoelzel
     */
    public class IRSwTToIDPProof extends DefaultProof {
        /** Constructor! */
        public IRSwTToIDPProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed intTRS into an equivalent IDP.";
        }
    }
}
