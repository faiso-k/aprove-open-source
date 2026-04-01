package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Removes leading & trailing nodes from Cdt graph, i.e. nodes which cannot be
 * reached from an SCC or from which no SCC is reachable.
 */
public class CdtLeafRemovalProcessor extends CdtProblemProcessor{

    private final boolean filterLeading;

    @ParamsViaArgumentObject
    public CdtLeafRemovalProcessor(final Arguments args) {
        this.filterLeading = args.filterLeading;
    }

    @Override
    protected boolean isCdtApplicable(final CdtProblem obl) {
        return !Options.certifier.isCpf();
    }

    @Override
    protected Result processCdt(final CdtProblem cdtProblem, final Abortion aborter)
            throws AbortionException {
        final BasicCdtGraph oldCdtGraph = cdtProblem.getGraph();
        final Graph<Cdt, BitSet> graph = oldCdtGraph.getGraph();

        final Set<Cdt> removedTrailingTuples = new LinkedHashSet<>();
        final Set<Cdt> removedLeadingTuples = new LinkedHashSet<>();
        {
            final Set<Node<Cdt>> removedTrailingNodes =
                    this.removeTrailingNodes(graph, cdtProblem.getS(), cdtProblem.getK());
            for (final Node<Cdt> node : removedTrailingNodes) {
                removedTrailingTuples.add(node.getObject());
                graph.removeNode(node);
            }

            final Set<Node<Cdt>> removedLeadingNodes =
                    this.removeLeadingNodes(graph, cdtProblem.getDefinedRSymbols());
            removedLeadingNodes.removeAll(removedTrailingNodes);
            for (final Node<Cdt> node : removedLeadingNodes) {
                removedLeadingTuples.add(node.getObject());
                graph.removeNode(node);
            }
        }

        if (removedLeadingTuples.isEmpty() && removedTrailingTuples.isEmpty()) {
            return ResultFactory.unsuccessful("Could not remove any node");
        }

        final BasicCdtGraph cdtGraph = oldCdtGraph.getSubgraph(graph.getNodes());
        final CdtProblem newCdtProblem = cdtProblem.createSubproblem(cdtGraph);
        final CdtLeafRemovalProof proof =
            new CdtLeafRemovalProof(
                    removedLeadingTuples, removedTrailingTuples);
        final Implication impl = (removedLeadingTuples.isEmpty()
                ? BothBounds.create()
                : ComplexityIfPolyImplication.create());
        return ResultFactory.proved(newCdtProblem,
                impl, proof);
}

    /**
     * Remove all nodes from the graph from which no cycles are reachable
     * and which are not relevant to the complexity of the system.
     */
    private Set<Node<Cdt>> removeTrailingNodes(final SimpleGraph<Cdt, ?> graph,
            final Set<Cdt> cdtS, final Set<Cdt> cdtK) {
        final ArrayList<Cycle<Cdt>> sccList =
            new ArrayList<Cycle<Cdt>>(graph.getSCCs(false));
        final Set<Node<Cdt>> cycleFollows = new HashSet<Node<Cdt>>();
        final Set<Node<Cdt>> trailingNodes = new HashSet<Node<Cdt>>();
        /* This works as graph.getSCCs() returns the nodes in reverse
         * topological order: If a node is followed by a SCC, this
         * SCC is visited therefore and hence its nodes are in
         * cycleFollows. */
        for (final Cycle<Cdt> scc : sccList) {
            if (scc.size() > 1) {
                cycleFollows.addAll(scc);
            } else {
                final Node<Cdt> node = scc.iterator().next();
                final Set<Node<Cdt>> outNodes = graph.getOut(node);

                boolean needed = false;
                if (outNodes.contains(node)) {
                    needed = true;
                } else if (!Collections.disjoint(outNodes, cycleFollows)) {
                    needed = true;
                } else if (cdtS.contains(node.getObject())) {
                    for (final Node<Cdt> inNode : graph.getIn(node)) {
                        final Cdt inCdt = inNode.getObject();
                        if (!cdtS.contains(inCdt) && !cdtK.contains(inCdt)) {
                            needed = true;
                        }
                    }
                }

                if (needed) {
                    cycleFollows.add(node);
                } else {
                    trailingNodes.add(node);
                }
            }
        }

        return trailingNodes;
    }


    private Set<Node<Cdt>> removeLeadingNodes(final SimpleGraph<Cdt, ?> graph, final Set<FunctionSymbol> definedRSymbols) {
        if (!this.filterLeading) {
            return Collections.emptySet();
        }

        final LinkedHashSet<Node<Cdt>> removed = new LinkedHashSet<Node<Cdt>>();

        final LinkedHashSet<Cycle<Cdt>> sccs = graph.getSCCs(false);
        /* topoSccs is in topological order: If A pops before B from topoSccs,
         * then there is no link from B to A */
        final Deque<Cycle<Cdt>> topoSccs = new ArrayDeque<Cycle<Cdt>>(sccs.size());
        for (final Cycle<Cdt> scc : sccs) {
            topoSccs.push(scc);
        }

        final Set<Node<Cdt>> nonRemovablePrecedes = new HashSet<Node<Cdt>>();
        while (!topoSccs.isEmpty()) {
            final Cycle<Cdt> scc = topoSccs.pop();
            if (scc.size() > 1) {
                nonRemovablePrecedes.addAll(scc);
            } else {
                final Node<Cdt> node = scc.iterator().next();
                final Set<Node<Cdt>> inNodes = graph.getIn(node);
                if (inNodes.contains(node)
                        || !Collections.disjoint(inNodes, nonRemovablePrecedes)
                        || CdtLeafRemovalProcessor.leadingNodeNecessary(node, definedRSymbols)) {
                    nonRemovablePrecedes.add(node);
                } else {
                    removed.add(node);
                    graph.removeNode(node);
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
    public static boolean leadingNodeNecessary(final Node<Cdt> node, final Set<FunctionSymbol> definedRSymbols) {
        final Rule r = node.getObject().getRule();
        final Set<FunctionSymbol> leftSyms = r.getLeft().getFunctionSymbols();
        final Set<FunctionSymbol> rightSyms = r.getRight().getFunctionSymbols();
        return (Collections.disjoint(leftSyms, definedRSymbols)
                && !Collections.disjoint(rightSyms, definedRSymbols));
    }

    public class CdtLeafRemovalProof extends CpxProof {

        private final Set<Cdt> leadingTuples;
        private final Set<Cdt> trailingTuples;

        public CdtLeafRemovalProof(final Set<Cdt> leadingTuples, final Set<Cdt> trailingTuples) {
            this.leadingTuples = leadingTuples;
            this.trailingTuples = trailingTuples;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            if (!this.leadingTuples.isEmpty()) {
                sb.append("Removed " + this.leadingTuples.size() + " leading nodes:");
                sb.append(o.set(this.leadingTuples, Export_Util.RULES));
            }
            if (!this.trailingTuples.isEmpty()) {
                sb.append("Removed " + this.trailingTuples.size() + " trailing nodes:");
                sb.append(o.set(this.trailingTuples, Export_Util.RULES));
            }
            return sb.toString();
        }

    }

    public static class Arguments {
        public boolean filterLeading = true;
    }

}
