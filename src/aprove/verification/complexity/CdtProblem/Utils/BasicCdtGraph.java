package aprove.verification.complexity.CdtProblem.Utils;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class BasicCdtGraph implements DOT_Able {

    /**
     * The underlying graph.
     *
     * The BitSet associated with an edge tells for which RHSArgs of
     * the tuple this edge exists.
     */
    private final Graph<Cdt, BitSet> graph;

    /**
     * Maps a node to some informations regarding the genesis of this node.
     *
     * Used by the heuristics of the transformation processors.
     */
    private final Map<Node<Cdt>, GraphHistory> history;

    private final IcapCalculator icap;

    private BasicCdtGraph(final Graph<Cdt, BitSet> g, final IcapCalculator icap,
            final Map<Node<Cdt>, GraphHistory> history) {
        this.graph = g;
        this.icap = icap;
        this.history = history;
    }

    public static BasicCdtGraph create(final Set<Cdt> tuples, final Set<Rule> rawRules) {

        final Graph<Cdt, BitSet> g = new Graph<Cdt, BitSet>();
        for (final Cdt tuple : tuples) {
            final Node<Cdt> node = new Node<Cdt>(tuple);
            g.addNode(node);
        }

        final CollectionMap<FunctionSymbol, Node<Cdt>> root2Node = new CollectionMap<FunctionSymbol, Node<Cdt>>();
        for (final Cdt tuple : tuples) {
            root2Node.add(tuple.getRule().getRootSymbol(), g.getNodeFromObject(tuple));
        }

        final IcapCalculator icap = new IcapCalculator(rawRules);

        /*
         * Approximate graph edge. Do this by comparing the root symbols
         * and defer more sophisticated stuff to probablyConnected.
         */
        for (final Node<Cdt> startNode : g.getNodes()) {
            final Set<Node<Cdt>> potentialEndNodes = new LinkedHashSet<Node<Cdt>>();
            for (final TRSFunctionApplication rhsArg : startNode.getObject().getRuleRHSArgs()) {
                potentialEndNodes.addAll(root2Node.getNotNull(rhsArg.getRootSymbol()));
            }
            for (final Node<Cdt> endNode : potentialEndNodes) {
                final BitSet connection = BasicCdtGraph.estimateEdge(startNode, endNode, icap);
                if (!connection.isEmpty()) {
                    g.addEdge(startNode, endNode, connection);
                }
            }
        }

        final Map<Node<Cdt>, GraphHistory> history = new LinkedHashMap<Node<Cdt>, GraphHistory>();
        for (final Node<Cdt> node : g.getNodes()) {
            history.put(node, GraphHistory.createEmpty(node.getObject()));
        }
        return new BasicCdtGraph(g, icap, history);
    }

    public Set<BasicCdtGraph> getComponents() {
        final Set<Node<Cdt>> nodes = new LinkedHashSet<Node<Cdt>>(this.graph.getNodes());
        final List<Set<Node<Cdt>>> components = new ArrayList<Set<Node<Cdt>>>();
        while (!nodes.isEmpty()) {
            final Set<Node<Cdt>> component = new LinkedHashSet<Node<Cdt>>();

            final Iterator<Node<Cdt>> it = nodes.iterator();
            final Node<Cdt> startNode = it.next();
            it.remove();

            /* compute forward nodes */
            final Queue<Node<Cdt>> todo = new ArrayDeque<Node<Cdt>>();
            todo.add(startNode);
            while (!todo.isEmpty()) {
                final Node<Cdt> node = todo.poll();
                component.add(node);
                final Set<Node<Cdt>> nextNodes = new LinkedHashSet<Node<Cdt>>(this.graph.getOut(node));
                nextNodes.addAll(this.graph.getIn(node));
                nextNodes.retainAll(nodes);
                nodes.removeAll(nextNodes);
                todo.addAll(nextNodes);
            }

            components.add(component);
        }

        if (Globals.useAssertions) {
            final int gSize = this.graph.getNodes().size();
            int cSize = 0;
            for (final Set<Node<Cdt>> c : components) {
                cSize += c.size();
                for (final Node<Cdt> n : c) {
                    final Set<Node<Cdt>> neighbors = new LinkedHashSet<Node<Cdt>>(this.graph.getIn(n));
                    neighbors.addAll(this.graph.getOut(n));
                    assert (this.graph.getNodes().containsAll(neighbors));
                }
            }
            assert (gSize == cSize);
        }

        final Set<BasicCdtGraph> res = new LinkedHashSet<BasicCdtGraph>();
        for (final Set<Node<Cdt>> component : components) {
            res.add(this.getSubgraph(component));
        }
        return res;
    }

    /**
     * Returns a map, which maps each SCC(*) of this graph to a new graph: A
     * graph containing the SCC and all nodes leading to this SCC.
     * <p>
     * (*) SCC means SCC with at least on edge (i.e. the usual definition for
     * dependency pairs/tuples).
     */
    public Map<Cycle<Cdt>, BasicCdtGraph> getReachingClosedSccs() {
        final Graph<Cdt, BitSet> graph = this.getGraph();

        /* SCCs in the graph-theoretic sense. In topological order */
        final ArrayList<Cycle<Cdt>> mathSccs = new ArrayList<Cycle<Cdt>>(graph.getSCCs(false));
        Collections.reverse(mathSccs);

        /* Maps each SCC to a number */
        final ArrayList<Cycle<Cdt>> nrToScc = new ArrayList<Cycle<Cdt>>();
        /* Maps each node to the number of the SCC it belongs to */
        final Map<Node<Cdt>, Integer> sccNodeToNr = new LinkedHashMap<Node<Cdt>, Integer>();
        for (final Cycle<Cdt> scc : mathSccs) {
            nrToScc.add(scc);
            final int idx = nrToScc.size() - 1;
            for (final Node<Cdt> n : scc) {
                sccNodeToNr.put(n, idx);
            }
        }

        /* All nodes leading to a SCC, including the SCC itself */
        final ArrayList<BitSet> nrToReachingNrs = new ArrayList<BitSet>();
        for (final Cycle<Cdt> scc : mathSccs) {
            final int sccIdx = sccNodeToNr.get(scc.iterator().next());

            final Set<Node<Cdt>> inNodes = new LinkedHashSet<Node<Cdt>>();
            for (final Node<Cdt> n : scc) {
                inNodes.addAll(graph.getIn(n));
            }
            inNodes.removeAll(scc);

            final BitSet reachingNrs = new BitSet(nrToScc.size());
            reachingNrs.set(sccIdx);
            for (final Node<Cdt> inNode : inNodes) {
                final Integer inNodeSccIdx = sccNodeToNr.get(inNode);
                /* mathSccs are iterated in topological order */
                reachingNrs.or(nrToReachingNrs.get(inNodeSccIdx));
            }
            nrToReachingNrs.add(sccIdx, reachingNrs);
        }

        final Map<Cycle<Cdt>, BasicCdtGraph> result = new LinkedHashMap<Cycle<Cdt>, BasicCdtGraph>();
        for (final ListIterator<BitSet> it = nrToReachingNrs.listIterator(); it.hasNext();) {
            final int nr = it.nextIndex();
            final BitSet bs = it.next();

            final Cycle<Cdt> scc = nrToScc.get(nr);
            /*
             * skip SCCs without an edge (i.e. SCCs, which are only mathematical
             * SCCs, not DP-SCCs)
             */
            if (scc.size() == 1) {
                final Node<Cdt> sccNode = scc.iterator().next();
                if (!graph.getOut(sccNode).contains(sccNode)) {
                    continue;
                }
            }

            final LinkedHashSet<Node<Cdt>> nodes = new LinkedHashSet<Node<Cdt>>();
            for (int i = bs.nextSetBit(0); i >= 0; i = bs.nextSetBit(i + 1)) {
                nodes.addAll(nrToScc.get(i));
            }
            result.put(scc, this.getSubgraph(nodes));
        }

        return result;
    }

    public ImmutableSet<Cdt> getTuples() {
        return ImmutableCreator.create(this.graph.getNodeObjects());
    }

    /**
     * Returns the transformation history of a node.
     *
     * May not be modified.
     */
    public GraphHistory getHistory(final Node<Cdt> node) {
        return this.history.get(node);
    }

    public IcapCalculator getIcap() {
        return new IcapCalculator(this.icap);
    }

    public BasicCdtGraph getSubgraph(final Set<Node<Cdt>> nodes) {
        final Map<Node<Cdt>, GraphHistory> history = new LinkedHashMap<Node<Cdt>, GraphHistory>();
        for (final Node<Cdt> node : nodes) {
            history.put(node, this.history.get(node));
        }
        return new BasicCdtGraph(this.graph.getSubGraph(nodes), this.icap, history);
    }

    /**
     * Returns a copy of the underlying graph.
     *
     * Nodes are shared, i.e. node labels may not be modified!
     */
    public Graph<Cdt, BitSet> getGraph() {
        return this.graph.getCopy();
    }

    /**
     * FIXME: Make a real copy of the graph, including the nodes!
     * FIXME: Move this to {@link Graph}?
     */
    public Graph<Cdt, BitSet> getCopyOfGraph() {
        final Set<Node<Cdt>> nodes = this.graph.getNodes();
        final Set<Edge<BitSet, Cdt>> edges = this.graph.getEdges();
        final Map<Node<Cdt>, Node<Cdt>> old2new = new LinkedHashMap<Node<Cdt>, Node<Cdt>>();
        for (final Node<Cdt> node : nodes) {
            old2new.put(node, new Node<Cdt>(node.getObject()));
        }
        final Set<Edge<BitSet, Cdt>> newEdges = new LinkedHashSet<Edge<BitSet, Cdt>>(edges.size());
        for (final Edge<BitSet, Cdt> edge : edges) {
            newEdges.add(new Edge<BitSet, Cdt>(old2new.get(edge.getStartNode()), old2new.get(edge.getEndNode()),
                edge.getObject()));
        }
        final Set<Node<Cdt>> newNodes = new LinkedHashSet<Node<Cdt>>(old2new.values());
        return new Graph<Cdt, BitSet>(newNodes, newEdges);
    }

    /**
     * Returns a transformed graph, where oldNode is replaced by nodes for
     * newTuples, For the edges of the new nodes, only nodes connected with oldNode
     * are considered (if node is connected to itself, also connections between
     * the new nodes are considered).
     */
    public BasicCdtGraph getTransformedGraph(final GraphHistory.Technique technique,
        final Node<Cdt> oldNode,
        final Set<Cdt> newTuples) {
        return this.getTransformedGraph(technique, Collections.singletonMap(oldNode, newTuples));
    }

    /**
     * Like multiple application of getTransformedGraph(Node, Set), but without
     * the overhead of copying the graph many times.
     */
    public BasicCdtGraph getTransformedGraph(final GraphHistory.Technique technique,
        final Map<Node<Cdt>, Set<Cdt>> transformations) {
        final Graph<Cdt, BitSet> g = this.getGraph();
        final IcapCalculator newIcap = new IcapCalculator(this.icap);

        final Map<Node<Cdt>, GraphHistory> newHistory = new LinkedHashMap<Node<Cdt>, GraphHistory>(this.history);

        for (final Map.Entry<Node<Cdt>, Set<Cdt>> transformation : transformations.entrySet()) {
            final Node<Cdt> oldNode = transformation.getKey();
            final Set<Cdt> newTuples = transformation.getValue();

            final Set<Node<Cdt>> newNodes = this.applyTransformation(g, newIcap, oldNode, newTuples);

            final GraphHistory histEntry = newHistory.remove(oldNode).createTransformed(technique);
            for (final Node<Cdt> node : newNodes) {
                newHistory.put(node, histEntry);
            }
        }
        return new BasicCdtGraph(g, newIcap, newHistory);
    }

    private Set<Node<Cdt>> applyTransformation(final Graph<Cdt, BitSet> g,
        final IcapCalculator newIcap,
        final Node<Cdt> oldNode,
        final Set<Cdt> newTuples) {
        final Set<Node<Cdt>> outNodes = g.getOut(oldNode);
        final Set<Node<Cdt>> inNodes = g.getIn(oldNode);
        g.removeNode(oldNode);

        boolean selfLoop = false;
        if (outNodes.remove(oldNode)) {
            selfLoop = true;
            inNodes.remove(oldNode);
        }

        final Set<Node<Cdt>> newNodes = new LinkedHashSet<Node<Cdt>>();
        for (final Cdt cdt : newTuples) {
            final Node<Cdt> newNode = new Node<Cdt>(cdt);
            newNodes.add(newNode);
            g.addNode(newNode);

            for (final Node<Cdt> outNode : outNodes) {
                this.addEstimatedEdge(g, newIcap, newNode, outNode);
            }
            for (final Node<Cdt> inNode : inNodes) {
                this.addEstimatedEdge(g, newIcap, inNode, newNode);
            }
        }

        if (selfLoop) {
            for (final Node<Cdt> startNode : newNodes) {
                for (final Node<Cdt> endNode : newNodes) {
                    this.addEstimatedEdge(g, newIcap, startNode, endNode);
                }
            }
        }

        return newNodes;
    }

    /**
     * Adds an estimated edge to the graph. The edge may not exist already!
     *
     * Returns true, if the edge was really added (and not discarded, because
     * the connection info was empty).
     */
    private boolean addEstimatedEdge(final Graph<Cdt, BitSet> g,
        final IcapCalculator newIcap,
        final Node<Cdt> startNode,
        final Node<Cdt> endNode) {
        final BitSet connection = BasicCdtGraph.estimateEdge(startNode, endNode, newIcap);
        if (!connection.isEmpty()) {
            final boolean added = g.addEdge(startNode, endNode, connection);
            if (Globals.useAssertions) {
                assert (added);
            }
            return true;
        }
        return false;
    }

    private static BitSet estimateEdge(final Node<Cdt> startNode,
        final Node<Cdt> endNode,
        final IcapCalculator icapCache) {
        final List<TRSTerm> cappedRhss = icapCache.getCappedRhs(startNode.getObject());
        final TRSTerm endLhs = endNode.getObject().getRuleLHS().renumberVariables(IcapAlgorithm.PREFIX_NOTCAP);
        final BitSet connection = new BitSet();
        for (final ListIterator<TRSTerm> it = cappedRhss.listIterator(); it.hasNext();) {
            final int idx = it.nextIndex();
            final TRSTerm cappedRhs = it.next();
            final TRSSubstitution mgu = cappedRhs.getMGU(endLhs);
            if (mgu != null && icapCache.getRules().termIsNormal(endLhs.applySubstitution(mgu))) {
                connection.set(idx);
            }
        }
        return connection;
    }

    @Override
    public String toDOT() {
        return this.graph.toDOT();
    }

}
