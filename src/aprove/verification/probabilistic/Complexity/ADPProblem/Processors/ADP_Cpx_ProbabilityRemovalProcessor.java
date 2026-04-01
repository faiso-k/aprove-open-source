package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import immutables.*;

/**
 * Probability Removal Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_ProbabilityRemovalProcessor extends ADP_Cpx_ProblemProcessor {

    private static class TupleComputeState {

        Map<Cdt, Rule> cdts;
        Set<FunctionSymbol> compoundSymbols;
        Set<FunctionSymbol> definedPSymbols;
        Set<FunctionSymbol> definedRSymbols;
        FreshNameGenerator fng;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem pqdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!pqdp.getInnermost() || !pqdp.isBasic()) {
            return false;
        }
        return pqdp.isNonProbabilistic();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processCpxADPProblem(final ADP_Cpx_Problem origPqdp, final Abortion aborter) throws AbortionException {
        final QTRSProblem newQtrs = origPqdp.getSwithQ().getNonProbAbstraction();

        final TupleComputeState state = new TupleComputeState();
        state.compoundSymbols = new LinkedHashSet<>(origPqdp.getP().size());
        state.definedRSymbols = ImmutableCreator.create(origPqdp.getSwithQ().getDefSymbolsOfR());
        state.definedPSymbols = ImmutableCreator.create(origPqdp.getAnnoMap().keySet());
        state.cdts = new LinkedHashMap<>(origPqdp.getP().size());
        state.fng = new FreshNameGenerator(origPqdp.getSignature(), FreshNameGenerator.DEPENDENCY_PAIRS);

        final Set<ProbabilisticRule> P = origPqdp.getP();
        for (final ProbabilisticRule depTuple : P) {
            for (final TRSTerm rhs : depTuple.getRight().getSupport()) {
                final Rule rule = Rule.create(depTuple.getLeft().renameAtAllMap(depTuple.getLeft().getPositions(), origPqdp.getDeAnnoMap()),
                    rhs.renameAtAllMap(rhs.getPositions(), origPqdp.getDeAnnoMap()));
                //TODO Check this!
                for (final TRSTerm term : rhs.getAnnoSubterms(origPqdp.getDeAnnoMap())) {
                    final List<Cdt> cdts = Collections
                        .singletonList(Cdt.createFromRule(state.fng, rule, new ArrayList<>(rhs.getAnnoSubtermsOnlyPositions(origPqdp.getDeAnnoMap()))));
                    for (final Cdt cdt : cdts) {
                        state.compoundSymbols.add(cdt.getCompoundSym());
                        state.cdts.put(cdt, rule);
                    }
                }
            }
        }
        final CdtProblem cdtProblem =
            CdtProblem.uncheckedCreate(newQtrs.getR(), state.cdts.keySet(), state.compoundSymbols, state.definedPSymbols, state.definedRSymbols);

        final CpxADP_ProbabilityRemovalProof prProof = new CpxADP_ProbabilityRemovalProof();

        return ResultFactory.proved(cdtProblem, UpperBound.create(), prProof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class CpxADP_ProbabilityRemovalProof extends ADP_SAST_Proof {

        private CpxADP_ProbabilityRemovalProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            res.append("We use the probability removal processor to move to dependecy tuples without probabilities."); // Add Citation;
            res.append(o.linebreak());
            res.append("As all rules have a trivial probability (1:r), we can transform it into a non-probabilistic DT problem");
            res.append(o.linebreak());
            return o.export(res.toString());
        }

    }

    public static class Arguments {

        public boolean beComplete = true;
        public boolean useApplicativeCeRules = true;
    }
}
