package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public abstract class CdtTransformationProcessor extends CdtProblemProcessor {

    private final boolean useHeuristics;
    private final int limit;

    @ParamsViaArgumentObject
    protected CdtTransformationProcessor(Arguments args) {
        this.limit = args.limit;
        this.useHeuristics = args.useHeuristics;
    }

    /**
     * Computes a transformation of the graph
     */
    protected abstract Transformation computeTransformation(State st, Node<Cdt> node);

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return !Options.certifier.isCpf();
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        State st = new State(cdtProblem);
        Set<Node<Cdt>> initialNodes = st.graph.getNodes();

        for (Node<Cdt> node : initialNodes) {
            Transformation trans = this.computeTransformation(st, node);
            if (trans == null) {
                continue;
            }

            Map<Node<Cdt>,Set<Cdt>> transMap =
                Collections.singletonMap(trans.oldNode, trans.newCdts);

            CdtProblem newCdtProblem = trans.complete
                    ? cdtProblem.createTransformedComplete(trans.technique, transMap)
                    : cdtProblem.createTransformedIncomplete(trans.technique, transMap);

            if (this.isSafe(cdtProblem, trans, newCdtProblem)) {
                return ResultFactory.proved(newCdtProblem,
                        BothBounds.create(), trans.proof);
            }
        }

        return ResultFactory.unsuccessful("Could not transform any node");

    }

    /**
     * Checks whether it is a good idea to perform this transformation.
     *
     * The heuristics are based on the safe heuristics described in
     * "Mechanizing and Improving Dependency Pairs".
     */
    protected boolean isSafe(CdtProblem oldProblem,
            Transformation trans,
            CdtProblem newProblem) {
        if (!this.useHeuristics) {
            return true;
        }

        BasicCdtGraph oldGraph = oldProblem.getGraph();
        BasicCdtGraph newGraph = newProblem.getGraph();

        GraphHistory history = oldGraph.getHistory(trans.oldNode);
        if (history.getTransformations(trans.technique) < this.limit) {
            return true;
        }

        LinkedHashSet<Cycle<Cdt>> oldSccs = oldGraph.getGraph().getSCCs();
        LinkedHashSet<Cycle<Cdt>> newSccs = newGraph.getGraph().getSCCs();

        /* Check whether there are less nodes in SCCs then before the
         * transformation */
        {
            int oldNodeCnt = 0;
            for (Cycle<Cdt> c : oldSccs) {
                oldNodeCnt += c.size();
            }

            int newNodeCnt = 0;
            for (Cycle<Cdt> c : newSccs) {
                newNodeCnt += c.size();
            }

            if (newNodeCnt < oldNodeCnt) {
                return true;
            }
        }

        /* Check whether the number of descendants of "original" DTs in SCCs is
         * less then before there transformation */
        {
            LinkedHashSet<Cdt> oldOrigCdts = new LinkedHashSet<Cdt>();
            for (Cycle<Cdt> c : oldSccs) {
                for (Node<Cdt> node : c) {
                    oldOrigCdts.add(oldGraph.getHistory(node).getOrigTuple());
                }
            }
            LinkedHashSet<Cdt> newOrigCdts = new LinkedHashSet<Cdt>();
            for (Cycle<Cdt> c : newSccs) {
                for (Node<Cdt> node : c) {
                    newOrigCdts.add(newGraph.getHistory(node).getOrigTuple());
                }
            }
            if (newOrigCdts.size() < oldOrigCdts.size()) {
                return true;
            }
        }

        return false;
    }

    protected static class State {
        BasicCdtGraph cdtGraph;
        final Graph<Cdt, BitSet> graph;
        final CdtProblem cdtProblem;
        final FreshNameGenerator fng;

        public State(CdtProblem cdtProblem) {
            this.cdtProblem = cdtProblem;
            this.cdtGraph = cdtProblem.getGraph();
            this.graph = this.cdtGraph.getGraph();
            this.fng = new FreshNameGenerator(cdtProblem.getSignature(),
                    FreshNameGenerator.APPEND_NUMBERS);

        }
    }

    protected static class Transformation {

        final boolean complete;
        final GraphHistory.Technique technique;
        final Node<Cdt> oldNode;
        final Set<Cdt> newCdts;
        final Proof proof;

        public Transformation(boolean complete,
                GraphHistory.Technique technique,
                Node<Cdt> oldNode,
                Set<Cdt> newCdts,
                Proof proof) {
            this.complete = complete;
            this.technique = technique;
            this.oldNode = oldNode;
            this.newCdts = newCdts;
            this.proof = proof;
        }

    }

    public static class Arguments {
        /**
         * Number of applications of this processor (per tuple) which are always
         * considered safe.
         */
        public int limit = 1;

        /**
         * Only apply this processor, if the heuristics tell us it is safe.
         */
        public boolean useHeuristics = true;
    }


}