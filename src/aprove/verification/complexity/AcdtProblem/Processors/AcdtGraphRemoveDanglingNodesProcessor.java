package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Removes leading & trailing nodes from Cdt graph, i.e. nodes which cannot be
 * reached from an SCC or from which no SCC is reachable.
 */
public class AcdtGraphRemoveDanglingNodesProcessor extends AcdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        BasicAcdtGraph oldCdtGraph = cdtProblem.getGraph();
        Graph<Acdt, BitSet> graph = oldCdtGraph.getGraph();
        int removedNodesCnt = GraphAlgorithms.removeTrailingNodes(graph).size();
        removedNodesCnt += this.removeLeadingNodes(graph, cdtProblem.getDefinedRSymbols());
        if (removedNodesCnt == 0) {
            return ResultFactory.unsuccessful("Could not remove any node");
        }
        BasicAcdtGraph cdtGraph = oldCdtGraph.getSubgraph(graph.getNodes());

        AcdtProblem newCdtProblem = cdtProblem.createSubproblem(cdtGraph);
        CdtGraphRemoveDanglingProof proof =
            new CdtGraphRemoveDanglingProof(
                    removedNodesCnt,
                    removedNodesCnt + graph.getNodes().size());
        return ResultFactory.proved(newCdtProblem,
                BothBounds.create(), proof);
    }

    private int removeLeadingNodes(SimpleGraph<Acdt, ?> graph, Set<FunctionSymbol> definedRSymbols) {
        LinkedHashSet<Cycle<Acdt>> sccs = graph.getSCCs(false);
        /* topoSccs is in topological order: If A pops before B from topoSccs,
         * then there is no link from B to A */
        Deque<Cycle<Acdt>> topoSccs = new ArrayDeque<Cycle<Acdt>>(sccs.size());
        for (Cycle<Acdt> scc : sccs) {
            topoSccs.push(scc);
        }

        int removed = 0;

        Set<Node<Acdt>> nonRemovablePrecedes = new HashSet<Node<Acdt>>();
        while (!topoSccs.isEmpty()) {
            Cycle<Acdt> scc = topoSccs.pop();
            if (scc.size() > 1) {
                nonRemovablePrecedes.addAll(scc);
            } else {
                Node<Acdt> node = scc.iterator().next();
                Set<Node<Acdt>> inNodes = graph.getIn(node);
                if (inNodes.contains(node)
                        || !Collections.disjoint(inNodes, nonRemovablePrecedes)
                        || AcdtGraphRemoveDanglingNodesProcessor.leadingNodeNecessary(node, definedRSymbols)) {
                    nonRemovablePrecedes.add(node);
                } else {
                    graph.removeNode(node);
                    removed++;
                }
            }
        }

        return removed;
    }

    /**
     * A leading node is necessary, if it can be the first tuple in a derivation
     * (i.e. its LHS does not contain any defined symbols) and removing it might
     * prevent some longer derivation (i.e. its RHS contains defined symbols)
     */
    public static boolean leadingNodeNecessary(Node<Acdt> node, Set<FunctionSymbol> definedRSymbols) {
        Rule r = node.getObject().getRule();
        Set<FunctionSymbol> leftSyms = r.getLeft().getFunctionSymbols();
        Set<FunctionSymbol> rightSyms = r.getRight().getFunctionSymbols();
        return (Collections.disjoint(leftSyms, definedRSymbols)
                && !Collections.disjoint(rightSyms, definedRSymbols));
    }

    public class CdtGraphRemoveDanglingProof extends DefaultProof {

        private final int removedCount;
        private final int originalCount;

        public CdtGraphRemoveDanglingProof(int removedCount, int originalCount) {
            this.removedCount = removedCount;
            this.originalCount = originalCount;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME Real proof!
            return "Removed " + this.removedCount + " of " + this.originalCount + " dangling nodes";
        }

    }
}
