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

/**
 *
 * @author Marc Brockschmidt
 */
public class ITRSDeepFSBisimulation extends ITRSFSMerger {
    /** Convenience class to represent possibly bisimilar elements. */
    public abstract static class PossiblyBisimilarElement { }

    /** Convenience class to represent possibly bisimilar variables. */
    public static class PossiblyBisimilarVariable extends PossiblyBisimilarElement {
        /** The wrapped variable. */
        private final TRSVariable var;

        /** @param v Variable to wrap. */
        public PossiblyBisimilarVariable(final TRSVariable v) { this.var = v; }

        /** {@inheritDoc} */
        @Override
        public String toString() {
            return this.var.toString();
        }

        /** {@inheritDoc} */
        @Override
        public int hashCode() {
            return this.var.hashCode();
        }

        /** {@inheritDoc} */
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
            final PossiblyBisimilarVariable other = (PossiblyBisimilarVariable) obj;
            if (this.var == null) {
                if (other.var != null) {
                    return false;
                }
            } else if (!this.var.equals(other.var)) {
                return false;
            }
            return true;
        }
    }

    /** Convenience class to represent possibly bisimilar function symbols. */
    public static class PossiblyBisimilarFS extends PossiblyBisimilarElement {
        /** The wrapped function symbol. */
        private final FunctionSymbol fs;

        /** @param f Function symbol to wrap. */
        public PossiblyBisimilarFS(final FunctionSymbol f) { this.fs = f; }

        /** @return the wrapped function symbol. */
        public FunctionSymbol getFs() {
            return this.fs;
        }

        /** {@inheritDoc} */
        @Override
        public String toString() {
            return this.fs.toString();
        }

        /** {@inheritDoc} */
        @Override
        public int hashCode() {
            return this.fs.hashCode();
        }

        /** {@inheritDoc} */
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
            final PossiblyBisimilarFS other = (PossiblyBisimilarFS) obj;
            if (this.fs == null) {
                if (other.fs != null) {
                    return false;
                }
            } else if (!this.fs.equals(other.fs)) {
                return false;
            }
            return true;
        }
    }

    @Override
    protected Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses (
            final ITRSProblem itrs, final Abortion aborter) throws AbortionException {
        return ITRSDeepFSBisimulation.getMergeClasses(itrs.getRuleAnalysis(), aborter);
    }


    public static Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses (
        final RuleAnalysis<GeneralizedRule> rules, final Abortion aborter) throws AbortionException {
        final SimpleGraph<PossiblyBisimilarElement, Set<Position>> graph = ITRSDeepFSBisimulation.createGraph(rules);

        if (graph.getNodes().isEmpty()) {
            return null;
        }
        final Collection<Set<Node<PossiblyBisimilarElement>>> initialPartition =
            ITRSDeepFSBisimulation.getInitialPartition(graph, rules.getPreDefinedMap());

        final IBisimulationAlgorithm<PossiblyBisimilarElement, Position> bisimAlg =
            new PartitionSplittingBisimulation<PossiblyBisimilarElement, Position>();
        final Collection<Set<Node<PossiblyBisimilarElement>>> bisim =
            bisimAlg.getBisimulation(graph, initialPartition, aborter);

        final Map<Set<FunctionSymbol>, FunctionSymbol> res =
            new LinkedHashMap<Set<FunctionSymbol>, FunctionSymbol>();
        final IDPPredefinedMap predefinedMap = rules.getPreDefinedMap();
        for (final Set<Node<PossiblyBisimilarElement>> eqClass : bisim) {
            //Boring eqClass:
            if (eqClass.size() < 2) {
                continue;
            }

            final LinkedHashSet<FunctionSymbol> fsEqClass =
                new LinkedHashSet<FunctionSymbol>();
            for (final Node<PossiblyBisimilarElement> n : eqClass) {
                if (n.getObject() instanceof PossiblyBisimilarFS) {
                    final FunctionSymbol fs =
                        ((PossiblyBisimilarFS) n.getObject()).getFs();
                    if (!predefinedMap.isPredefined(fs)) {
                        fsEqClass.add(fs);
                    }
                } else {
                    assert (fsEqClass.size() == 0)
                    : "Variable and function symbol bisimilar!";
                }
            }
            if (fsEqClass.size() > 1) {
                res.put(fsEqClass, fsEqClass.iterator().next());
            }
        }

        return new Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication>(res, YNMImplication.SOUND);
    }


    /**
     * @param graph the graph describing the rewrite relation and subterm
     *  connections.
     * @return partition for our bisimulation, where function symbols are in one
     *  class per arity and all variables are in one class.
     */
    @SuppressWarnings("unchecked")
    private static Collection<Set<Node<PossiblyBisimilarElement>>> getInitialPartition(
            final SimpleGraph<PossiblyBisimilarElement, Set<Position>> graph,
            final IDPPredefinedMap predefinedMap) {
        final CollectionMap<Integer, Node<PossiblyBisimilarElement>> partitioning =
            new CollectionMap<Integer, Node<PossiblyBisimilarElement>>();
        final Set<Node<PossiblyBisimilarElement>> variables =
            new LinkedHashSet<Node<PossiblyBisimilarElement>>();
        final Collection<Set<Node<PossiblyBisimilarElement>>> res =
            new LinkedHashSet<Set<Node<PossiblyBisimilarElement>>>();

        for (final Node<PossiblyBisimilarElement> node : graph.getNodes()) {
            if (node.getObject() instanceof PossiblyBisimilarVariable) {
                variables.add(node);
            } else {
                final FunctionSymbol wrappedFs =
                    ((PossiblyBisimilarFS) node.getObject()).getFs();
                if (wrappedFs.getName().startsWith("java")
                        || wrappedFs.getName().equals("ARRAY")
                        || wrappedFs.getName().equals("NULL")) {
                    res.add(Collections.singleton(node));
                } else if (predefinedMap.isPredefined(wrappedFs)) {
                    res.add(Collections.singleton(node));
                } else {
                    partitioning.add(wrappedFs.getArity(), node);
                }
            }
        }

        res.addAll((Collection) partitioning.values());
        if (!variables.isEmpty()) {
            res.add(variables);
        }
        return res;
    }

    /**
     * Add a new connection to the graph, taking care of all caching, node and
     * edge label creation issues.
     * @param graph the graph in which we add the connection
     * @param elementToNodeMap map representing the node cache
     * @param t1 source of the edge
     * @param p edge label to add
     * @param t2 target of the edge
     */
    private static void addConnection(
            final SimpleGraph<PossiblyBisimilarElement, Set<Position>> graph,
            final LinkedHashMap<PossiblyBisimilarElement, Node<PossiblyBisimilarElement>> elementToNodeMap,
            final FunctionSymbol t1,
            final Position p,
            final TRSTerm t2) {
        final PossiblyBisimilarElement e1 = new PossiblyBisimilarFS(t1);
        final PossiblyBisimilarElement e2;
        if (t2.isVariable()) {
            e2 = new PossiblyBisimilarVariable((TRSVariable) t2);
        } else {
            e2 = new PossiblyBisimilarFS(((TRSFunctionApplication) t2).getRootSymbol());
        }
        final Node<PossiblyBisimilarElement> n1 =
            ITRSDeepFSBisimulation.getOrCreateNode(e1, graph, elementToNodeMap);
        final Node<PossiblyBisimilarElement> n2 =
            ITRSDeepFSBisimulation.getOrCreateNode(e2, graph, elementToNodeMap);

        Set<Position> edgeLabel =
            graph.removeEdgeAndReturnLabel(n1, n2);
        if (edgeLabel == null) {
            edgeLabel = new LinkedHashSet<Position>();
        }
        edgeLabel.add(p);
        graph.addEdge(n1, n2, edgeLabel);
    }

    /**
     * @param e some element
     * @param graph the graph in which we store the nodes;
     * @param elementToNodeMap map representing the node cache
     * @return the cached node for <code>e</code> or a new node which is now
     *  also stored in the graph and cache.
     */
    private static Node<PossiblyBisimilarElement> getOrCreateNode(final PossiblyBisimilarElement e,
            final SimpleGraph<PossiblyBisimilarElement, Set<Position>> graph,
            final LinkedHashMap<PossiblyBisimilarElement, Node<PossiblyBisimilarElement>> elementToNodeMap) {
        if (elementToNodeMap.containsKey(e)) {
            return elementToNodeMap.get(e);
        }
        final Node<PossiblyBisimilarElement> newNode =
            new Node<PossiblyBisimilarElement>(e);
        elementToNodeMap.put(e, newNode);
        graph.addNode(newNode);
        return newNode;
    }

    /**
     * Add connections to subterm symbols to the graph (for all subterms).
     * @param graph the graph in which we add the connections
     * @param elementToNodeMap map representing the node cache
     * @param t some term
     */
    private static void addSubTermEdges(
            final SimpleGraph<PossiblyBisimilarElement, Set<Position>> graph,
            final LinkedHashMap<PossiblyBisimilarElement, Node<PossiblyBisimilarElement>> elementToNodeMap,
            final TRSTerm t) {
        for (final TRSTerm term : t.getSubTerms()) {
            //No need to do more. Skip this one.
            if (term.isVariable()) {
                continue;
            }

            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            final FunctionSymbol fs = fa.getRootSymbol();

            for (final Pair<Position, TRSTerm> q : fa.getPositionsWithSubTerms()) {
                final Position subPos = q.x;
                final TRSTerm subTerm = q.y;
                ITRSDeepFSBisimulation.addConnection(graph, elementToNodeMap, fs, subPos, subTerm);
            }
        }
    }

    /**
     * Create the initial graph, where nodes are all function symbols and
     * variables occurring in the system.
     * Edges are connecting function symbols to occurring subterms (i.e. the
     * symbols or variables there), where the edge label contains the position
     * that connects the two.
     * Rules are represented with edges from the lhs root symbol to the rhs
     * root symbol/variable and labeled by the empty position.
     * @param rules The rule system for our bisimulation.
     * @return a graph suitable for deep function symbol bisimulation.
     */
    private static SimpleGraph<PossiblyBisimilarElement, Set<Position>> createGraph(final RuleAnalysis<GeneralizedRule> rules) {
        final SimpleGraph<PossiblyBisimilarElement, Set<Position>> graph =
            new SimpleGraph<PossiblyBisimilarElement, Set<Position>>();

        final LinkedHashMap<PossiblyBisimilarElement,
                      Node<PossiblyBisimilarElement>> elementToNodeMap =
            new LinkedHashMap<PossiblyBisimilarElement,
                              Node<PossiblyBisimilarElement>>();

        final int ruleCounter = 0;
        for (final GeneralizedRule rule : rules.getRules()) {
            final GeneralizedRule renamedRule =
                rule.getWithRenumberedVariables(ruleCounter + "_");

            ITRSDeepFSBisimulation.addSubTermEdges(graph, elementToNodeMap, renamedRule.getLeft());
            ITRSDeepFSBisimulation.addConnection(graph, elementToNodeMap,
                    renamedRule.getLeft().getRootSymbol(),
                    Position.create(new int[0]),
                    renamedRule.getRight());
            ITRSDeepFSBisimulation.addSubTermEdges(graph, elementToNodeMap, renamedRule.getRight());
        }

        return graph;
    }
}
