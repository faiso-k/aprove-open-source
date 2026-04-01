package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * For each node of the Cdt graph, remove all tuple-subterms of the
 * RHS which do not have an outgoing edge (i.e. none of the edges
 * of the node "belongs" to the tuple-subterm).
 *
 * Should be used after the {@link AcdtGraphRemoveDanglingNodesProcessor}.
 */
public class AcdtGraphRemoveTrailingTuplepartsProcessor extends AcdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Graph<Acdt, BitSet> graph = cdtProblem.getGraph().getGraph();
        int deletedParts = 0;
        Map<Node<Acdt>, Set<Acdt>> transformations = new LinkedHashMap<Node<Acdt>, Set<Acdt>>();
        for (Node<Acdt> node : graph.getNodes()) {
            Acdt oldCdt = node.getObject();
            ArrayList<TRSFunctionApplication> args = oldCdt.getRuleRHSArgs();
            BitSet removeTupleparts = new BitSet(args.size());
            removeTupleparts.set(0, args.size());
            for (Node<Acdt> outNode : graph.getOut(node)) {
                removeTupleparts.andNot(graph.getEdgeObject(node, outNode));
            }
            if (!removeTupleparts.isEmpty()) {
                deletedParts += removeTupleparts.cardinality();
                Acdt newCdt = oldCdt.filter(removeTupleparts);
                transformations.put(node, Collections.singleton(newCdt));
            }
        }


        if (deletedParts == 0) {
            return ResultFactory.unsuccessful("Could not remove any tuple part");
        }

        AcdtProblem newCdtProblem = cdtProblem.createTransformed(transformations);
        CdtGraphRemoveTrailingProof proof =
            new CdtGraphRemoveTrailingProof(deletedParts);
        return ResultFactory.proved(newCdtProblem,
                BothBounds.create(), proof);
    }

    public class CdtGraphRemoveTrailingProof extends DefaultProof {

        private final int removedCount;

        public CdtGraphRemoveTrailingProof(int removedCount) {
            this.removedCount = removedCount;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME Real proof!
            return "Removed " + this.removedCount + " trailing tuple parts";
        }

    }
}
