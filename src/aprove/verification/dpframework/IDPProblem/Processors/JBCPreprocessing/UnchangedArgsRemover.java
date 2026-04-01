package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This processor analyses which arguments are left unchanged throughout the
 * whole SCC. These can be removed, if they are not read in some other part of
 * the TRS.
 * @author cotto
 */
public class UnchangedArgsRemover extends ITRSProcessor {
    /**
     * The proof for this processor giving information about the unused
     * arguments and how they are removed.
     * @author cotto
     */
    private class UnchangedArgsProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param itrsProblem the ITRSProblem that has been processed
         * @param removedArgs information about removed arguments.
         * @param names information about name changes.
         */
        public UnchangedArgsProof(
                final ITRSProblem itrsProblem,
                final CollectionMap<FunctionSymbol, Integer> removedArgs,
                final Map<FunctionSymbol, FunctionSymbol> names) {
            super(itrsProblem, removedArgs, names);
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
                    "Some arguments are removed because they are unused and unchanged throughout the whole SCC.");
            sb.append(eu.linebreak());
            super.export(eu, sb);
            return sb.toString();
        }
    }


    /**
     * Yes, we can. For innermost ITRSs.
     * @param itrs any itrs problem
     * @return true (sometimes)
     */
    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return itrs.isNfQSubsetEqNfR();
    }

    /**
     * @param itrs some itrs problem
     * @param aborter an aborter
     * @throws AbortionException never.
     * @return the resulting ITRS problem where some arguments are removed (or
     * "unsuccessful").
     */
    @Override
    protected Result processITRSProblem(final ITRSProblem itrs,
        final Abortion aborter) throws AbortionException {
        /*
         * Check if the ITRS has the right format. If so, create a handy graph
         * out of it and get some nice properties of this graph.
         */
        final Pair<MultiGraph<FunctionSymbol, GeneralizedRule>, Collection<Cycle<FunctionSymbol>>> itrsGraph =
            HelperClass.toGraph(itrs, false);
        if (itrsGraph == null) {
            return ResultFactory.unsuccessful();
        }
        final MultiGraph<FunctionSymbol, GeneralizedRule> graph = itrsGraph.x;
        final Collection<Cycle<FunctionSymbol>> sccs = itrsGraph.y;

        /*
         * Now do some real work. For every pair of function symbols that is
         * used in at least one rule along the SCC, a map of unchanged arguments
         * is constructed:
         * f(x, y, z) -> g(h(z), 1@z, z, y, x) results in
         * 1 -> 5
         * 2 -> 4
         * 3 -> 3 (will be removed later because z occurs in h(z)
         *
         * If the pair occurs more than once, the map is restricted to the
         * intersection of the "no change" edges.
         */
        final CollectionMap<FunctionSymbol, Integer> unchangedPositions =
            new CollectionMap<FunctionSymbol, Integer>();
        for (final Cycle<FunctionSymbol> scc : sccs) {
            final CollectionMap<FunctionSymbol, Integer> unchangedPositionsSCC =
                HelperClass.getUnchangedPositions(graph, scc);
            unchangedPositions.putAll(unchangedPositionsSCC);
        }
        if (unchangedPositions.isEmpty()) {
            return ResultFactory.unsuccessful();
        }
        final Pair<ITRSProblem, Map<FunctionSymbol, FunctionSymbol>> pair =
            HelperClass.getResultingITRS(itrs, unchangedPositions);
        final UnchangedArgsProof proof =
            new UnchangedArgsProof(itrs, unchangedPositions, pair.y);
        return ResultFactory.proved(pair.x,
            YNMImplication.EQUIVALENT, proof);
    }
}
