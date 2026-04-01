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
public class ITRSWeakFSBisimulation extends ITRSFSMerger {

    @Override
    protected Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses (
            final ITRSProblem itrs, final Abortion aborter) throws AbortionException {
        return ITRSWeakFSBisimulation.getMergeClasses(itrs.getRuleAnalysis(), aborter);
    }

    public static Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses (
        final RuleAnalysis<GeneralizedRule> rules, final Abortion aborter) throws AbortionException {
        final SimpleGraph<Object, Set<Number>> graph = ITRSWeakFSBisimulation.createGraph(rules, aborter);
        if (graph.getNodes().isEmpty()) {
            return null;
        }
        final IBisimulationAlgorithm<Object, Number> bisimAlg = new PartitionSplittingBisimulation<Object, Number>();
        final Collection<Set<Node<Object>>> initialPartition = ITRSWeakFSBisimulation.getInitialPartition(rules, graph, aborter);
        final Collection<Set<Node<Object>>> bisim = bisimAlg.getBisimulation(graph, initialPartition, aborter);

        final Map<Set<FunctionSymbol>, FunctionSymbol> merges = new LinkedHashMap<Set<FunctionSymbol>, FunctionSymbol>();

        for (final Set<Node<Object>> equivalenceClass : bisim) {
            if (equivalenceClass.size() > 1) {
                if (equivalenceClass.iterator().next().getObject() instanceof FunctionSymbol) {
                    final Set<FunctionSymbol> mergeFs = new LinkedHashSet<FunctionSymbol>();
                    for (final Node<Object> node : equivalenceClass) {
                        mergeFs.add((FunctionSymbol) node.getObject());
                    }

                    merges.put(mergeFs, mergeFs.iterator().next());
                }
            }
        }

        return new Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> (merges, YNMImplication.SOUND);
    }

    private static Collection<Set<Node<Object>>> getInitialPartition(final RuleAnalysis<GeneralizedRule> rules,
            final SimpleGraph<Object, Set<Number>> graph, final Abortion aborter) {
        final Map<Integer, Set<Node<Object>>> partitioning = new LinkedHashMap<Integer, Set<Node<Object>>>();

        final Set<Node<Object>> variableClass = new LinkedHashSet<Node<Object>>();

        int singleton = -1;

        for (final Node<Object> node : graph.getNodes()) {
            if (node.getObject() instanceof FunctionSymbol) {
                final FunctionSymbol fs = (FunctionSymbol) node.getObject();
                if (rules.getPreDefinedMap().isPredefined(fs)) {
                    partitioning.put(singleton--, Collections.singleton(node));
                } else {
                    Set<Node<Object>> set = partitioning.get(fs.getArity());
                    if (set == null) {
                        set = new LinkedHashSet<Node<Object>>();
                        partitioning.put(fs.getArity(), set);
                    }
                    set.add(node);
                }
            } else if (node.getObject() instanceof TRSVariable) {
                variableClass.add(node);
            } else {
                partitioning.put(singleton--, Collections.singleton(node));
            }
        }

        partitioning.put(singleton--, variableClass);

        return partitioning.values();
    }

    private static SimpleGraph<Object, Set<Number>> createGraph(final RuleAnalysis<GeneralizedRule> rules, final Abortion aborter) {
        final SimpleGraph<Object, Set<Number>> graph = new SimpleGraph<Object, Set<Number>>();
        final Map<FunctionSymbol, Node<Object>> fsToNode = new LinkedHashMap<FunctionSymbol, Node<Object>>();
        final Map<FunctionSymbol, Node<Object>> fsToMatching = new LinkedHashMap<FunctionSymbol, Node<Object>>();
        for (final FunctionSymbol fs : rules.getFunctionSymbols()) {
            final Node<Object> node = new Node<Object>(fs);
            graph.addNode(node);
            fsToNode.put(fs, node);

            final Node<Object> matchingNode = new Node<Object>(new MatchingSymbol(fs));
            graph.addNode(matchingNode);
            fsToMatching.put(fs, matchingNode);
        }
        int ruleRenumber = 0;
        for (final GeneralizedRule rule : rules.getRules()) {
            final Map<TRSVariable, TRSVariable> ruleRenumberMap = new LinkedHashMap<TRSVariable, TRSVariable>();
            final ImmutablePair<? extends TRSFunctionApplication, Integer> ruleLeftRenumbered =
                rule.getLeft().renumberVariables(ruleRenumberMap , "x", ruleRenumber);
            final ImmutablePair<? extends TRSTerm, Integer> ruleRightRenumbered =
                rule.getRight().renumberVariables(ruleRenumberMap , "x", ruleLeftRenumbered.y);
            ruleRenumber = ruleRightRenumbered.y;
            final HashMap<TRSVariable, Node<Object>> varToNode = new LinkedHashMap<TRSVariable, Node<Object>>();
            for (final TRSVariable var : ruleRenumberMap.values()) {
                final Node<Object> node = new Node<Object>(var);
                graph.addNode(node);
                varToNode.put(var, node);
            }
            if (!ruleRightRenumbered.x.isVariable()) {
                final TRSFunctionApplication nodeRight = (TRSFunctionApplication) ruleRightRenumbered.x;
                final Node<Object> fromNode = fsToNode.get(ruleLeftRenumbered.x.getRootSymbol());
                final Node<Object> toNode = fsToNode.get(nodeRight.getRootSymbol());
                if (!graph.contains(fromNode, toNode)) {
                    graph.addEdge(fromNode, toNode, new LinkedHashSet<Number>());
                }
                graph.getEdge(fromNode, toNode).getObject().add(0);
            }
            ITRSWeakFSBisimulation.addTermEdges(graph, fsToNode, varToNode, fsToMatching, false, ruleLeftRenumbered.x);
            ITRSWeakFSBisimulation.addTermEdges(graph, fsToNode, varToNode, fsToMatching, false, ruleRightRenumbered.x);
        }
        return graph;
    }

    private static void addTermEdges(final SimpleGraph<Object, Set<Number>> graph,
        final Map<FunctionSymbol, Node<Object>> fsToNode, final HashMap<TRSVariable, Node<Object>> varToNode, final Map<FunctionSymbol, Node<Object>> fsToMatching, final boolean leftMatching, final TRSTerm t) {
        if (t.isVariable()) {
            return;
        }

        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        final Node<Object> fromNode = fsToNode.get(fa.getRootSymbol());

        for (int i = fa.getArguments().size() - 1; i >= 0; i--){
            final TRSTerm arg = fa.getArgument(i);
            Node<Object> toNode;
            if (arg.isVariable()) {
                toNode = varToNode.get(arg);
            } else {
                toNode = fsToNode.get(((TRSFunctionApplication) arg).getRootSymbol());

                if (leftMatching) {
                    final Node<Object> matchingNode = fsToMatching.get(fa.getRootSymbol());

                    if (!graph.contains(toNode, matchingNode)) {
                        graph.addEdge(toNode, matchingNode, new LinkedHashSet<Number>());
                    }
                    graph.getEdge(toNode, matchingNode).getObject().add(0);
                }
            }

            if (!graph.contains(fromNode, toNode)) {
                graph.addEdge(fromNode, toNode, new LinkedHashSet<Number>());
            }
            graph.getEdge(fromNode, toNode).getObject().add(i + 1);

            if (!graph.contains(toNode, fromNode)) {
                graph.addEdge(toNode, fromNode, new LinkedHashSet<Number>());
            }
            graph.getEdge(toNode, fromNode).getObject().add(-i - 1);

            ITRSWeakFSBisimulation.addTermEdges(graph, fsToNode, varToNode, fsToMatching, leftMatching, arg);
        }
    }


    private static class MatchingSymbol {

        private final FunctionSymbol fs;

        public MatchingSymbol(final FunctionSymbol fs) {
            this.fs = fs;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.fs == null) ? 0 : this.fs.hashCode());
            return result;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final MatchingSymbol other = (MatchingSymbol) obj;
            return this.fs.equals(other.fs);
        }

    }
}
