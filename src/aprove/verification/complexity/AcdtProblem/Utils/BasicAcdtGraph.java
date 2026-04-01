package aprove.verification.complexity.AcdtProblem.Utils;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class BasicAcdtGraph implements DOT_Able {

    /**
     * The underlying graph.
     *
     * The BitSet associated with an edge tells for which RHSArgs of
     * the tuple this edge exists.
     */
    private final Graph<Acdt, BitSet> graph;

    private final IcapCalculator icap;

    private BasicAcdtGraph(Graph<Acdt, BitSet> g, IcapCalculator icap) {
        this.graph = g;
        this.icap = icap;
    }

    public static BasicAcdtGraph create(Graph <Acdt, BitSet> g, IcapCalculator icap) {
        return new BasicAcdtGraph(g, icap);
    }

    public static BasicAcdtGraph create(
            Set<Acdt> tuples, Set<Rule> rawRules) {

        Graph<Acdt, BitSet> g = new Graph<Acdt, BitSet>();
        for (Acdt tuple : tuples) {
            Node<Acdt> node = new Node<Acdt>(tuple);
            g.addNode(node);
        }

        CollectionMap<FunctionSymbol, Node<Acdt>> root2Node =
            new CollectionMap<FunctionSymbol, Node<Acdt>>();
        for (final Acdt tuple : tuples) {
            root2Node.add(tuple.getRule().getRootSymbol(),
                g.getNodeFromObject(tuple));
        }

        IcapCalculator icap = new IcapCalculator(rawRules);

        /*
         * Approximate graph edge. Do this by comparing the root symbols
         * and defer more sophisticated stuff to probablyConnected.
         */
        for (Node<Acdt> startNode : g.getNodes()) {
            Set<Node<Acdt>> potentialEndNodes = new LinkedHashSet<Node<Acdt>>();
            for (TRSFunctionApplication rhsArg : startNode.getObject().getRuleRHSArgs()) {
                potentialEndNodes.addAll(root2Node.getNotNull(rhsArg.getRootSymbol()));
            }
            for (Node<Acdt> endNode : potentialEndNodes) {
                BitSet connection = BasicAcdtGraph.estimateEdge(startNode, endNode, icap);
                if (!connection.isEmpty()) {
                    g.addEdge(startNode, endNode, connection);
                }
            }
        }

        return new BasicAcdtGraph(g, icap);
    }

    public Set<BasicAcdtGraph> getComponents() {
        Set<Node<Acdt>> nodes = new LinkedHashSet<Node<Acdt>>(this.graph.getNodes());
        List<Set<Node<Acdt>>> components = new ArrayList<Set<Node<Acdt>>>();
        while (!nodes.isEmpty()) {
            Set<Node<Acdt>> component = new LinkedHashSet<Node<Acdt>>();

            Iterator<Node<Acdt>> it = nodes.iterator();
            Node<Acdt> startNode = it.next();
            it.remove();

            /* compute forward nodes */
            Queue<Node<Acdt>> todo = new ArrayDeque<Node<Acdt>>();
            todo.add(startNode);
            while (!todo.isEmpty()) {
                Node<Acdt> node = todo.poll();
                component.add(node);
                Set<Node<Acdt>> nextNodes = new LinkedHashSet<Node<Acdt>>(this.graph.getOut(node));
                nextNodes.addAll(this.graph.getIn(node));
                nextNodes.retainAll(nodes);
                nodes.removeAll(nextNodes);
                todo.addAll(nextNodes);
            }

            components.add(component);
        }

        if (Globals.useAssertions) {
            int gSize = this.graph.getNodes().size();
            int cSize = 0;
            for (Set<Node<Acdt>> c : components) {
                cSize += c.size();
                for (Node<Acdt> n : c) {
                    Set<Node<Acdt>> neighbors = new LinkedHashSet<Node<Acdt>>(this.graph.getIn(n));
                    neighbors.addAll(this.graph.getOut(n));
                    assert(this.graph.getNodes().containsAll(neighbors));
                }
            }
            assert (gSize == cSize);
        }

        Set<BasicAcdtGraph> res = new LinkedHashSet<BasicAcdtGraph>();
        for (Set<Node<Acdt>>component : components) {
            res.add(this.getSubgraph(component));
        }
        return res;
    }

    public ImmutableSet<Acdt> getTuples() {
        return ImmutableCreator.create(this.graph.getNodeObjects());
    }

    public IcapCalculator getIcap() {
        return new IcapCalculator(this.icap);
    }

    public BasicAcdtGraph getSubgraph(Set<Node<Acdt>> nodes) {
        return new BasicAcdtGraph(this.graph.getSubGraph(nodes), this.icap);
    }

    /**
     * Returns a copy of the underlying graph.
     *
     * Nodes are shared, i.e. node labels may not be modified!
     */
    public Graph<Acdt, BitSet> getGraph() {
        return this.graph.getCopy();
    }

    /**
     * FIXME: Make a real copy of the graph, including the nodes!
     * FIXME: Move this to {@link Graph}?
     */
    public Graph<Acdt, BitSet> getCopyOfGraph() {
        Set<Node<Acdt>> nodes = this.graph.getNodes();
        Set<Edge<BitSet, Acdt>> edges = this.graph.getEdges();
        Map<Node<Acdt>,Node<Acdt>> old2new =
            new LinkedHashMap<Node<Acdt>, Node<Acdt>>();
        for (Node<Acdt>node : nodes) {
            old2new.put(node, new Node<Acdt>(node.getObject()));
        }
        Set<Edge<BitSet, Acdt>> newEdges =
            new LinkedHashSet<Edge<BitSet,Acdt>>(edges.size());
        for (Edge<BitSet, Acdt> edge : edges) {
            newEdges.add(new Edge<BitSet, Acdt>(
                    old2new.get(edge.getStartNode()),
                    old2new.get(edge.getEndNode()),
                    edge.getObject()));
        }
        Set<Node<Acdt>> newNodes = new LinkedHashSet<Node<Acdt>>(old2new.values());
        return new Graph<Acdt, BitSet>(newNodes, newEdges);
    }

    /**
     * Returns a transformed graph, were node is replaced by nodes for
     * newTuples, For the edges of the new nodes, only nodes connected with node
     * are considered (if node is connected to itself, also connections between
     * the new nodes are considered).
     */
    public BasicAcdtGraph getTransformedGraph(Node<Acdt> oldNode, Set<Acdt> newTuples) {
        return this.getTransformedGraph(Collections.singletonMap(oldNode, newTuples));
    }

    /**
     * Like multiple application of getTransformedGraph(Node, Set), but without
     * the overhead of copying the graph many times.
     */
    public BasicAcdtGraph getTransformedGraph(Map<Node<Acdt>, Set<Acdt>> transformations) {
        Graph<Acdt, BitSet> g = this.getGraph();
        IcapCalculator newIcap = new IcapCalculator(this.icap);

        for (Map.Entry<Node<Acdt>, Set<Acdt>> transformation : transformations.entrySet()) {
            Node<Acdt> oldNode = transformation.getKey();
            Set<Acdt> newTuples = transformation.getValue();

            this.applyTransformation(g, newIcap, oldNode, newTuples);
        }
        return new BasicAcdtGraph(g, newIcap);
    }

    private void applyTransformation(Graph<Acdt, BitSet> g, IcapCalculator newIcap,
            Node<Acdt> oldNode, Set<Acdt> newTuples) {
        Set<Node<Acdt>> outNodes = g.getOut(oldNode);
        Set<Node<Acdt>> inNodes = g.getIn(oldNode);
        g.removeNode(oldNode);

        boolean selfLoop = false;
        if (outNodes.remove(oldNode)) {
            selfLoop = true;
            inNodes.remove(oldNode);
        }

        Set<Node<Acdt>> newNodes = new LinkedHashSet<Node<Acdt>>();
        for (Acdt cdt : newTuples) {
            Node<Acdt> newNode = new Node<Acdt>(cdt);
            newNodes.add(newNode);
            g.addNode(newNode);

            for (Node<Acdt> outNode : outNodes) {
                this.addEstimatedEdge(g, newIcap, newNode, outNode);
            }
            for (Node<Acdt> inNode : inNodes) {
                this.addEstimatedEdge(g, newIcap, inNode, newNode);
            }
        }

        if (selfLoop) {
            for (Node<Acdt> startNode : newNodes) {
                for (Node<Acdt> endNode : newNodes) {
                    this.addEstimatedEdge(g, newIcap, startNode, endNode);
                }
            }
        }
    }

    /**
     * Adds an estimated edge to the graph. The edge may not exist already!
     *
     * Returns true, if the edge was really added (and not discarded, because
     * the connection info was empty).
     */
    private boolean addEstimatedEdge(Graph<Acdt, BitSet> g, IcapCalculator newIcap,
            Node<Acdt> startNode, Node<Acdt> endNode) {
        BitSet connection = BasicAcdtGraph.estimateEdge(startNode, endNode, newIcap);
        if (!connection.isEmpty()) {
            boolean added = g.addEdge(startNode, endNode, connection);
            if (Globals.useAssertions) {
                assert(added);
            }
            return true;
        }
        return false;
    }

    private static BitSet estimateEdge(Node<Acdt> startNode, Node<Acdt> endNode,
            IcapCalculator icapCache) {
        List<TRSTerm> cappedRhss =
            icapCache.getCappedRhs(startNode.getObject());
        TRSTerm endLhs = endNode.getObject().getRuleLHS().renumberVariables(IcapAlgorithm.PREFIX_NOTCAP);
        BitSet connection = new BitSet();
        for (ListIterator<TRSTerm> it = cappedRhss.listIterator(); it.hasNext();) {
            int idx = it.nextIndex();
            TRSTerm cappedRhs = it.next();
            if (cappedRhs.unifies(endLhs)) {
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
