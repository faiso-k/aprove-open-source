package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor removes arguments that can't influence termination. TODO:
 * There's a TeXed proof and a complete explanation for this around, but the URI
 * to that is not stable yet.
 * @author Martin Plücker
 */
public class ITRSFilterProcessor extends ITRSProcessor {

    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments {

        public volatile IIDPFilterHeuristic filterHeuristic;

        public Arguments() {
            final IdpCand1FilterHeuristic.Arguments args = new IdpCand1FilterHeuristic.Arguments();
            args.filterRelations = false;
            this.filterHeuristic = new IdpCand1FilterHeuristic(args);
        }
    }

    /**
     * The proof for this processor giving information about the removed
     * positions.
     * @author Martin Plücker
     */
    private class ITRSFilterProcessorProof extends ArgumentsRemovalProof {
        private final IIDPFilterHeuristic filterHeuristic;

        /**
         * Create a new proof.
         * @param filterHeuristic the heuristic that has been used to select filtered positions
         * @param removedArgs maps function symbols to the list of removed argument positions
         * @param names maps old function names to new ones
         */
        public ITRSFilterProcessorProof(
                final ITRSProblem itrsProblem,
                final IIDPFilterHeuristic filterHeuristic,
                final CollectionMap<FunctionSymbol, Integer> removedArgs,
                final Map<FunctionSymbol, FunctionSymbol> names) {
            super(itrsProblem, removedArgs, names);
            this.filterHeuristic = filterHeuristic;
        }

        /**
         * @return the proof as a nice string representation.
         * @param eu an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb =
                new StringBuilder(
                    "We filter according the heuristic ");
            sb.append(this.filterHeuristic.export(eu,
                super.getItrsProblem().getPredefinedMap(), level));
            sb.append(eu.linebreak());
            super.export(eu, sb);
            return sb.toString();
        }
    }

    /**
     * The heuristic used for filtering.
     */
    private final IIDPFilterHeuristic filterHeuristic;

    /**
     * Create a new processor instance.
     * @param arguments object holding parameters for this processor
     */
    @ParamsViaArgumentObject
    public ITRSFilterProcessor(final Arguments arguments) {
        this.filterHeuristic = arguments.filterHeuristic;
    }

    /**
     * Yes, we can.
     * @param itrs any itrs
     * @return true
     */
    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    /**
     * Start working on some IDP problem.
     * @param ruleAnalysis rule analysis for the IDP
     * @param aborter an aborter
     * @return two sets corresponding to a filtered P and R. null if nothing was
     *  filtered.
     * @throws AbortionException never.
     */
    public Triple<Set<GeneralizedRule>, Set<GeneralizedRule>, QTermSet> processIDPRuleAnalysis(final IDPRuleAnalysis ruleAnalysis, final Abortion aborter)
            throws AbortionException {
        // For every function symbol mark the positions that can be deleted:
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<FunctionSymbol, Integer>();
        boolean removedAnything = false;
        for (final FunctionSymbol fs : ruleAnalysis.getFunctionSymbols()) {
            final Collection<Integer> posToRemove = this.filterHeuristic.getFilteredPositions(ruleAnalysis, fs);
            removedAnything = removedAnything || !posToRemove.isEmpty();
            positionsToBeRemoved.put(fs, posToRemove);
        }

        if (!removedAnything) {
            // No argument can be removed
            return null;
        }

        // Construct the result
        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> pPair =
            HelperClass.getResultingRules(
                    ruleAnalysis.getPAnalysis().getRules(),
                    ruleAnalysis.getPreDefinedMap(),
                    positionsToBeRemoved,
                    new LinkedHashSet<FunctionSymbol>(ruleAnalysis.getFunctionSymbols()));

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> rPair =
            HelperClass.getResultingRules(
                    ruleAnalysis.getRAnalysis().getRules(),
                    ruleAnalysis.getPreDefinedMap(),
                    positionsToBeRemoved,
                    new LinkedHashSet<FunctionSymbol>(ruleAnalysis.getFunctionSymbols()));

        final QTermSet newQ = HelperClass.getNewQ(rPair.x);

        return new Triple<Set<GeneralizedRule>, Set<GeneralizedRule>, QTermSet>(pPair.x, rPair.x, newQ);
    }


    /**
     * Start working on the given ITRS.
     * @param itrs some ITRS
     * @param aborter an aborter
     * @return a new ITRS in which positions which (more or less obviously)
     *  don't influence termination were removed.
     * @throws AbortionException never.
     */
    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter)
            throws AbortionException {

        // For every function symbol mark the positions that can be deleted:
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<FunctionSymbol, Integer>();
        boolean removedAnything = false;
        final IDPRuleAnalysis ruleAnalysis = IDPRuleAnalysis.createFromR(itrs.getRuleAnalysis(), itrs.getQ());
        for (final FunctionSymbol fs : itrs.getRuleAnalysis().getFunctionSymbols()) {
            final Collection<Integer> posToRemove = this.filterHeuristic.getFilteredPositions(ruleAnalysis, fs);
            removedAnything = removedAnything || !posToRemove.isEmpty();
            positionsToBeRemoved.put(fs, posToRemove);
        }

        if (!removedAnything) {
            // No argument can be removed
            return ResultFactory.unsuccessful();
        }

        // Construct the result
        final Pair<ITRSProblem, Map<FunctionSymbol, FunctionSymbol>> pair =
            HelperClass.getResultingITRS(itrs, positionsToBeRemoved);

        final ITRSFilterProcessorProof proof =
            new ITRSFilterProcessorProof(itrs, this.filterHeuristic, positionsToBeRemoved, pair.y);

        return ResultFactory.proved(pair.x, YNMImplication.SOUND, proof);
    }
}
