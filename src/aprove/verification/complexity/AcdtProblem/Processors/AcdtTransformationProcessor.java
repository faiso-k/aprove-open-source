package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public abstract class AcdtTransformationProcessor extends AcdtProblemProcessor {

    /**
     * Computes a transformation of the graph
     */
    protected abstract Transformation computeTransformation(State st, Node<Acdt> node);

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        State st = new State(cdtProblem);
        Set<Node<Acdt>> initialNodes = st.graph.getNodes();

        for (Node<Acdt> node : initialNodes) {
            Transformation trans = this.computeTransformation(st, node);
            if (trans == null) {
                // FIXME: Need some heuristics in here.
                continue;
            }

            AcdtProblem newCdtProblem = cdtProblem.createTransformed(trans.nodeTransformations);

            return ResultFactory.proved(newCdtProblem,
                    BothBounds.create(), trans.proof);
        }

        return ResultFactory.unsuccessful("Could not transform any node");

    }

    protected static class State {
        BasicAcdtGraph cdtGraph;
        final Graph<Acdt, BitSet> graph;
        final AcdtProblem cdtProblem;
        final FreshNameGenerator fng;

        public State(AcdtProblem cdtProblem) {
            this.cdtProblem = cdtProblem;
            this.cdtGraph = cdtProblem.getGraph();
            this.graph = this.cdtGraph.getGraph();
            this.fng = new FreshNameGenerator(cdtProblem.getSignature(),
                    FreshNameGenerator.APPEND_NUMBERS);

        }
    }

    protected static class Transformation {

        final Map<Node<Acdt>,Set<Acdt>> nodeTransformations;
        final Proof proof;

        public Transformation(Map<Node<Acdt>, Set<Acdt>> singletonMap,
                Proof proof) {
            this.nodeTransformations = singletonMap;
            this.proof = proof;
        }

    }
}