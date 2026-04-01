package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
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
 * Should be used before the {@link CdtLeafRemovalProcessor}.
 */
public class CdtRhsSimplificationProcessor extends CdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return !Options.certifier.isCpf();
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Graph<Cdt, BitSet> graph = cdtProblem.getGraph().getGraph();
        int deletedParts = 0;
        Map<Node<Cdt>, Set<Cdt>> transformations = new LinkedHashMap<Node<Cdt>, Set<Cdt>>();
        for (Node<Cdt> node : graph.getNodes()) {
            Cdt oldCdt = node.getObject();
            List<TRSFunctionApplication> args = oldCdt.getRuleRHSArgs();
            BitSet removeTupleparts = new BitSet(args.size());
            removeTupleparts.set(0, args.size());
            for (Node<Cdt> outNode : graph.getOut(node)) {
                removeTupleparts.andNot(graph.getEdgeObject(node, outNode));
            }
            if (!removeTupleparts.isEmpty()) {
                deletedParts += removeTupleparts.cardinality();
                Cdt newCdt = oldCdt.filter(removeTupleparts);
                transformations.put(node, Collections.singleton(newCdt));
            }
        }


        if (deletedParts == 0) {
            return ResultFactory.unsuccessful("Could not remove any tuple part");
        }

        CdtProblem newCdtProblem =
            cdtProblem.createTransformedComplete(null, transformations);
        CdtRhsSimplificationProcessorProof proof =
            new CdtRhsSimplificationProcessorProof(deletedParts);
        return ResultFactory.proved(newCdtProblem,
                BothBounds.create(), proof);
    }

    public class CdtRhsSimplificationProcessorProof extends CpxProof {

        private final int removedCount;

        public CdtRhsSimplificationProcessorProof(int removedCount) {
            this.removedCount = removedCount;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME Real proof!
            return "Removed " + this.removedCount + " trailing tuple parts";
        }

    }
}
