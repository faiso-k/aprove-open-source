package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.bisimulation.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class ITRSFSBisimulation extends ITRSFSMerger {

    @Override
    protected Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses (
            final ITRSProblem itrs, final Abortion aborter) throws AbortionException {
        return ITRSFSBisimulation.getMergeClasses(itrs.getRuleAnalysis(), aborter);
    }

    public static Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses (
        final RuleAnalysis<GeneralizedRule> rules, final Abortion aborter) throws AbortionException {
        final SimpleGraph<GeneralizedRule, Object> graph = ITRSFSBisimulation.createGraph(rules, aborter);

        if (graph.getNodes().isEmpty()) {
            return null;
        }
        final IBisimulationAlgorithm bisimAlg = new PartitionSplittingBisimulation();
        final Collection<Set<Node<GeneralizedRule>>> initialPartition = ITRSFSBisimulation.getInitialPartition(rules, graph, aborter);
        final Collection<Set<Node<GeneralizedRule>>> bisim = bisimAlg.getBisimulation(graph, initialPartition, aborter);

        final BidirectionalMap<FunctionSymbol, Set<FunctionSymbol>> merges = ITRSFSBisimulation.initializeMerges(rules.getDefinedSymbols());

        for (final Set<Node<GeneralizedRule>> nodes : bisim) {
            final Set<FunctionSymbol> mergeLeft = new LinkedHashSet<FunctionSymbol>();
            final Set<FunctionSymbol> mergeRight = new LinkedHashSet<FunctionSymbol>();
            for (final Node<GeneralizedRule> node : nodes) {
                final GeneralizedRule rule = node.getObject();
                mergeLeft.add(rule.getRootSymbol());
                if (!rule.getRight().isVariable()) {
                    mergeRight.add(((TRSFunctionApplication) rule.getRight()).getRootSymbol());
                }
            }
            ITRSFSBisimulation.addMergeClass(mergeLeft, merges);
            ITRSFSBisimulation.addMergeClass(mergeRight, merges);
        }

        // cleanup merges
        final Iterator<Set<FunctionSymbol>> i = merges.keySetRL().iterator();
        while (i.hasNext()) {
            if (i.next().size() < 2) {
                i.remove();
            }
        }
        return new Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication>(merges.getRLMap(), YNMImplication.SOUND);
    }

    private static BidirectionalMap<FunctionSymbol, Set<FunctionSymbol>> initializeMerges(
            final ImmutableSet<FunctionSymbol> definedSymbols) {
        final BidirectionalMap<FunctionSymbol, Set<FunctionSymbol>> res = new BidirectionalMap<FunctionSymbol, Set<FunctionSymbol>>();
        final LinkedHashSet<FunctionSymbol> eqClass = new LinkedHashSet<FunctionSymbol>(definedSymbols);

        for (final FunctionSymbol fs : definedSymbols) {
            res.putLR(fs, eqClass);
        }

        return res;
    }

    private static void addMergeClass(final Set<FunctionSymbol> newClass,
            final BidirectionalMap<FunctionSymbol, Set<FunctionSymbol>> merges) {
        for (final FunctionSymbol classFs : newClass) {
            final Set<FunctionSymbol> currentClass = merges.getLR(classFs);
            if (currentClass != null) {
                final LinkedHashSet<FunctionSymbol> removeFromClass = new LinkedHashSet<FunctionSymbol>(currentClass);
                removeFromClass.removeAll(newClass);

                for (final FunctionSymbol removedFs : removeFromClass) {
                    merges.putLR(removedFs, removeFromClass);
                }

                currentClass.removeAll(removeFromClass);

                for (final FunctionSymbol remainingFs : currentClass) {
                    merges.putLR(remainingFs, currentClass);
                }
            }
        }
    }

    private static Collection<Set<Node<GeneralizedRule>>> getInitialPartition(final RuleAnalysis<GeneralizedRule> rules,
            final SimpleGraph<GeneralizedRule, Object> graph, final Abortion aborter) {
        final Map<Pair<List<TRSTerm>, List<TRSTerm>>, Set<Node<GeneralizedRule>>> partitioning = new LinkedHashMap<Pair<List<TRSTerm>,List<TRSTerm>>, Set<Node<GeneralizedRule>>>();
        for (final Node<GeneralizedRule> node : graph.getNodes()) {
            final GeneralizedRule rule = node.getObject();
            if (!rule.getRight().isVariable()) {
                final TRSFunctionApplication faRight = (TRSFunctionApplication) rule.getRhsInStandardRepresentation();
                final Pair<List<TRSTerm>, List<TRSTerm>> key = new Pair<List<TRSTerm>, List<TRSTerm>>(rule.getLhsInStandardRepresentation().getArguments(), faRight.getArguments());
                Set<Node<GeneralizedRule>> partition = partitioning.get(key);
                if (partition == null) {
                    partition = new LinkedHashSet<Node<GeneralizedRule>>();
                    partitioning.put(key, partition);
                }
                partition.add(node);
            }
        }
        return partitioning.values();
    }

    private static SimpleGraph<GeneralizedRule, Object> createGraph(final RuleAnalysis<GeneralizedRule> rules, final Abortion aborter) {
        final SimpleGraph<GeneralizedRule, Object> graph = new SimpleGraph<GeneralizedRule, Object>();
        for (final GeneralizedRule rule : rules.getRules()) {
            final Node<GeneralizedRule> node = new Node<GeneralizedRule>(rule);
            graph.addNode(node);
        }
        for (final Node<GeneralizedRule> node : graph.getNodes()) {
            final GeneralizedRule nodeRule = node.getObject();
            if (!nodeRule.getRight().isVariable()) {
                final TRSFunctionApplication nodeRight = (TRSFunctionApplication) nodeRule.getRight();
                final Set<FunctionSymbol> rightFunctionSymbols = nodeRight.getFunctionSymbols();

                for (final Node<GeneralizedRule> toNode : graph.getNodes()) {
                    if (rightFunctionSymbols.contains(toNode.getObject().getRootSymbol())) {
                        graph.addEdge(node, toNode, Collections.singleton(null));
                    }
                }
            }
        }

        // delete final nodes
        final Set<Node<GeneralizedRule>> finalNodes =
            new LinkedHashSet<Node<GeneralizedRule>>();

        for (final Node<GeneralizedRule> node : graph.getNodes()) {
            if (graph.getOutEdges(node).isEmpty()) {
                finalNodes.add(node);
                for (final Pair<Position, TRSTerm> p : node.getObject().getRight().getPositionsWithSubTerms()) {
                    final Position pos = p.x;
                    final TRSTerm t = p.y;
                    if (!pos.isEmptyPosition()
                            && (t instanceof TRSFunctionApplication)
                            && rules.getDefinedSymbols().contains(((TRSFunctionApplication) t).getRootSymbol())) {
                        finalNodes.remove(node);
                        break;
                    }
                }
            }
        }
        for (final Node<GeneralizedRule> node : finalNodes) {
            graph.removeNode(node);
        }
        return graph;
    }

}
