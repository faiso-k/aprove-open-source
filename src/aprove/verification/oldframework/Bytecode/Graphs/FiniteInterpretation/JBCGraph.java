package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * SimpleGraph-avoiding representation of JBC (termination) graphs.
 *
 * @author Marc Brockschmidt, Thies Strothmann
 */
public class JBCGraph {
    /**
     * A mapping from states to nodes in this graph. The value set of this
     * map is the set of nodes of this graph.
     */
    private final BidirectionalMap<State, Node> states_nodes;

    /**
     * Creates a new, empty graph.
     */
    public JBCGraph() {
        this.states_nodes = new BidirectionalMap<>();
    }

    /**
     * @param s state to add to the graph.
     * @return true iff the state was not yet contained in the graph.
     */
    public boolean addState(final State s) {
        s.initializeDeletionListeners();
        return this.addNode(new Node(s));
    }

    /**
     * @param n node to add to the graph
     * @return true iff the node was not yet contained in the graph.
     */
    public boolean addNode(final Node n) {
        final State s = n.getState();
        if (this.states_nodes.containsKeyLR(s)) {
            return false;
        }
        this.states_nodes.putLR(s, n);
        return true;
    }

    /**
     * @param n node to remove from the graph
     * @return true iff the node existed in the graph
     */
    public boolean removeNode(final Node n) {
        n.remove();
        return removeNodeInternal(n);
    }

    protected boolean removeNodeInternal(final Node n) {
        State s = this.states_nodes.removeRL(n);
        if (s == null) {
            return false;
        }
        s.notifyDeletionListeners();
        return true;
    }

    /**
     * This method requires the nodes to already exists in the Graph
     * This is required by the subclass MethodGraph
     * @param e edge to add to the graph
     * @return true iff the edge was not yet contained in the graph.
     */
    public boolean addEdge(final Edge e) {
        //Ensure start and end are in the graph:
        assert (this.containsNode(e.getStart()));
        assert (this.containsNode(e.getEnd()));

        final boolean addedOutgoing = e.getStart().addOutgoingEdge(e);
        final boolean addedIncoming = e.getEnd().addIncomingEdge(e);

        assert (addedOutgoing == addedIncoming) : "Graph structures not consistent!";
        return addedOutgoing;
    }

    /**
     * @param s start of the edge to add.
     * @param l label of the edge to add.
     * @param e end of the edge to add.
     * @return true iff the edge was not yet contained in the graph.
     */
    public boolean addEdge(final State s, final EdgeInformation l, final State e) {
        Node sNode = states_nodes.getLR(s);
        Node eNode = states_nodes.getLR(e);
        return this.addEdge(new Edge(sNode, l, eNode));
    }

    /**
     * @param sN start node of the edge to add.
     * @param l label of the edge to add.
     * @param eN end node of the edge to add.
     * @return true iff the edge was not yet contained in the graph.
     */
    public boolean addEdge(final Node sN, final EdgeInformation l, final Node eN) {
        return this.addEdge(new Edge(sN, l, eN));
    }

    /**
     * Contrary to addEdge, this method will create new nodes in the Graph if necessary
     * @param e edge to add to the graph. Creates fresh copied
     */
    public void createCopiedEdge(final Edge edge) {
        State start = edge.getStart().getState();
        State end = edge.getEnd().getState();
        this.addState(start);
        this.addState(end);
        this.addEdge(start, edge.getLabel(), end);
    }

    /**
     * @param edge some edge in the graph.
     */
    public void removeEdge(final Edge edge) {
        edge.getStart().removeOutgoingEdge(edge);
        edge.getEnd().removeIncomingEdge(edge);
    }

    /**
     * @return the set of all nodes in this graph.
     */
    public Collection<Node> getNodes() {
        return this.states_nodes.keySetRL();
    }

    /**
     * @return the number of all nodes in this graph.
     */
    public int getNodeNumber() {
        return this.states_nodes.size();
    }

    /**
     * @return the set of all edges in this graph.
     */
    public Collection<Edge> getEdges() {
        final Set<Edge> res = new LinkedHashSet<>();
        for (final Node n : this.getNodes()) {
            res.addAll(n.getOutEdges());
        }
        return res;
    }

    /**
     * @param s some state
     * @return the corresponding node in the graph.
     */
    public Node getNode(final State s) {
        return this.states_nodes.getLR(s);
    }

    /**
     * @param n some node
     * @return true if this node is in the graph.
     */
    public boolean containsNode(final Node n) {
        return this.states_nodes.containsKeyRL(n);
    }

    /**
     * @param s some state
     * @return true if there is a corresponding node in the graph.
     */
    public boolean containsState(final State s) {
        return this.states_nodes.containsKeyLR(s);
    }

    /**
     * Checks whether the graph contains a path from start to end.
     * <P>
     * Note: There is always a path (of length 0) from a node to itself, even if
     * there is no such edge.
     * @param start Start node of the path.
     * @param end End node of the path.
     * @param allowEmptyPaths if true, an empty path is allowed.
     * @param filter a filter deciding which edges may be selected (may be null,
     * means "every edge is allowed")
     * @return <code>true</code> if the graph contains such a path,
     * <code>false</code> otherwise
     */
    public static boolean hasPath(
        final Node start,
        final Node end,
        final boolean allowEmptyPaths,
        final EdgeFilter filter)
    {
        final Set<Node> done = new LinkedHashSet<>();
        final LinkedList<Node> todo = new LinkedList<>();

        if (allowEmptyPaths) {
            todo.push(start);
            done.add(start);
        } else {
            for (final Edge e : start.getOutEdges()) {
                final Node target = e.getEnd();
                if (filter == null || filter.selectEdge(start, target, e.getLabel())) {
                    done.add(target);
                    todo.push(target);
                }

            }
        }

        while (!todo.isEmpty()) {
            final Node node = todo.pop();
            if (node.equals(end)) {
                return true;
            }
            for (final Edge e : node.getOutEdges()) {
                final Node target = e.getEnd();
                if (filter == null || filter.selectEdge(start, target, e.getLabel())) {
                    if (done.add(target)) {
                        todo.push(target);
                    }
                }
            }
        }

        return false;

    }

    /**
     * Determine all nodes reachable from a given set of start nodes. breadth-first search
     *
     * @param sourceNodes set of nodes for which we want to determine the
     *  reachable nodes.
     * @return all nodes reachable from a node within <code>sourceNodes</code>.
     *  The returned set may be modified.
     */
    public static Set<Node> determineReachableNodes(final Collection<Node> sourceNodes) {
        return determineReachableNodes(sourceNodes, null);
    }


    /**
     * Determine all nodes reachable from a given set of start nodes. breadth-first search
     *
     * @param sourceNodes set of nodes for which we want to determine the
     *  reachable nodes.
     * @param filter a filter which edges may be selected
     * @return all nodes reachable from a node within <code>sourceNodes</code>.
     *  The returned set may be modified.
     */
    public static Set<Node> determineReachableNodes(final Collection<Node> sourceNodes, final EdgeFilter filter) {
        final Set<Node> result = new LinkedHashSet<>(sourceNodes);
        final Queue<Node> todo = new LinkedList<>();
        todo.addAll(sourceNodes);
        while (!todo.isEmpty()) {
            final Node node = todo.remove();
            for (final Edge e : node.getOutEdges()) {
                final Node target = e.getEnd();
                if (filter == null || filter.selectEdge(node, target, e.getLabel())) {
                    if (result.add(target)) {
                        todo.add(target);
                    }
                }
            }
        }
        return result;
    }

    /**
     * Determine all nodes reaching a given set of end nodes. breadth-first search
     *
     * @param targetNodes set of nodes for which we want to determine the
     *  reaching nodes.
     * @param filter a filter which edges may be selected
     * @return all nodes reaching a node within <code>targetNodes</code>.
     *  The returned set may be modified.
     */
    public static Set<Node> determineReachingNodes(final Collection<Node> targetNodes, final EdgeFilter filter) {
        final Set<Node> result = new LinkedHashSet<>(targetNodes);
        final Queue<Node> todo = new LinkedList<>();
        todo.addAll(targetNodes);
        while (!todo.isEmpty()) {
            final Node node = todo.remove();
            for (final Edge e : node.getInEdges()) {
                final Node source = e.getStart();
                if (filter.selectEdge(source, node, e.getLabel())) {
                    if (result.add(source)) {
                        todo.add(source);
                    }
                }
            }
        }
        return result;
    }

    /**
     * @param nodes a set of nodes contained in the current graph.
     * @return a new graph only containing nodes from <code>nodes</code> and
     *  edges containing them.
     */
    public JBCGraph getSubGraph(final Set<Node> nodes) {
        final JBCGraph subgraph = new JBCGraph();
        final Map<Node, Node> oldToNewMap = new LinkedHashMap<>();
        for (final Node oldNode : nodes) {
            final Node newNode = new Node(oldNode);
            subgraph.addNode(newNode);
            oldToNewMap.put(oldNode, newNode);
        }

        for (final Edge e : this.getEdges()) {
            final Node start = e.getStart();
            final Node end = e.getEnd();
            if (nodes.contains(start) && nodes.contains(end)) {
                subgraph.addEdge(oldToNewMap.get(start), e.getLabel(), oldToNewMap.get(end));
            }
        }

        return subgraph;
    }

    /**
     * @param edges a set of edges contained in the current graph.
     * @return a new graph only containing edges from <code>edges</code> and
     *  nodes contained in them.
     */
    public static JBCGraph getSubGraphByEdges(final Set<Edge> edges) {
        final JBCGraph subgraph = new JBCGraph();
        final Map<Node, Node> oldToNewMap = new LinkedHashMap<>();

        for (final Edge oldEdge : edges) {
            final Node oldStartNode = oldEdge.getStart();
            Node newStartNode = oldToNewMap.get(oldStartNode);
            if (newStartNode == null) {
                newStartNode = new Node(oldStartNode);
                subgraph.addNode(newStartNode);
                oldToNewMap.put(oldStartNode, newStartNode);
            }

            final Node oldEndNode = oldEdge.getEnd();
            Node newEndNode = oldToNewMap.get(oldEndNode);
            if (newEndNode == null) {
                newEndNode = new Node(oldEndNode);
                subgraph.addNode(newEndNode);
                oldToNewMap.put(oldEndNode, newEndNode);
            }

            subgraph.addEdge(newStartNode, oldEdge.getLabel(), newEndNode);
        }

        return subgraph;
    }

    /////////////////////// Start of SCC computation ///////////////////////////
    /**
     * @return set of sccs in the following order: if a scc is returned
     * before another, then from the first scc there is no path to the later scc
     */
    public LinkedHashSet<Set<Node>> getSCCs() {
        return this.getSCCs(null);
    }

    /**
     * @param filter a possible filter on which edges may be used (may be null)
     * @return set of sccs in the following order: if a scc is returned
     * before another, then from the first scc there is no path to the later scc
     */
    public LinkedHashSet<Set<Node>> getSCCs(final EdgeFilter filter) {
        int n = this.states_nodes.size();
        final Set<Node> visitedNodes = new LinkedHashSet<>(n);
        final List<Node> sortedNodes = new ArrayList<>(n);

        for (final Node node : this.states_nodes.keySetRL()) {
            this.visitFirst(node, visitedNodes, sortedNodes, filter);
        }

        // okay, now traverse in reverse order to compute Sccs
        visitedNodes.clear();
        final LinkedHashSet<Set<Node>> allSccs = new LinkedHashSet<>();
        while (n != 0) {
            n--;
            final Node node = sortedNodes.get(n);
            if (visitedNodes.contains(node)) {
                // we already visited this node
                continue;
            }
            final Set<Node> currentScc = new LinkedHashSet<>();
            for (final Edge outgoingEdge : node.getOutEdges()) {
                final Node target = outgoingEdge.getEnd();
                if (filter == null || filter.selectEdge(node, target, outgoingEdge.getLabel())) {
                    this.visitSecond(target, currentScc, visitedNodes, filter);
                }
            }
            if (!visitedNodes.add(node)) {
                allSccs.add(currentScc);
            }

        }
        return allSccs;
    }

    private
        void
        visitFirst(final Node node, final Set<Node> visited, final List<Node> collect, final EdgeFilter filter)
    {
        if (visited.add(node)) {
            for (final Edge inEdge : node.getInEdges()) {
                final Node source = inEdge.getStart();
                if (filter == null || filter.selectEdge(source, node, inEdge.getLabel())) {
                    this.visitFirst(source, visited, collect, filter);
                }
            }
            collect.add(node);
        }
    }

    private void visitSecond(
        final Node node,
        final Set<Node> currentScc,
        final Set<Node> visited,
        final EdgeFilter filter)
    {
        if (visited.add(node)) {
            currentScc.add(node);
            for (final Edge outEdge : node.getOutEdges()) {
                final Node target = outEdge.getEnd();
                if (filter == null || filter.selectEdge(node, target, outEdge.getLabel())) {
                    this.visitSecond(target, currentScc, visited, filter);
                }
            }
        }
    }

    //////////////////////// End of SCC computation ////////////////////////////

    public static Set<List<Edge>> getAllPathsBetween(final Node start, final Node end, final EdgeFilter filter) {
        final Set<List<Edge>> res = new LinkedHashSet<>();
        final Queue<LinkedList<Edge>> todo = new LinkedList<>();

        //Initialize todo:
        for (final Edge edge : start.getOutEdges()) {
            if (filter == null || filter.selectEdge(start, edge.getEnd(), edge.getLabel())) {
                final LinkedList<Edge> initialPath = new LinkedList<>();
                initialPath.add(edge);
                todo.add(initialPath);
            }
        }

        nextPath: while (!todo.isEmpty()) {
            final LinkedList<Edge> path = todo.poll();
            final Node reachedNode = path.getLast().getEnd();

            //We are done:
            if (reachedNode == end) {
                res.add(path);
                continue;
            }

            //We have been here before:
            for (final Edge foundEdge : path) {
                if (foundEdge.getStart().equals(reachedNode)) {
                    continue nextPath;
                }
            }

            //We have to recurse:
            for (final Edge edge : reachedNode.getOutEdges()) {
                if (filter == null || filter.selectEdge(start, edge.getEnd(), edge.getLabel())) {
                    final LinkedList<Edge> newPath = new LinkedList<>(path);
                    newPath.add(edge);
                    todo.add(newPath);
                }
            }
        }

        return res;
    }

    public static Set<List<Edge>> getAllPathsBetween(final Node start, final Node end) {
        return JBCGraph.getAllPathsBetween(start, end, null);
    }

    /**
     * @param interestingNodes set of nodes
     * @return the set of edges in this graph where both end and start are part of the set <code>interestingNodes</code>
     */
    public Set<? extends Edge> getEdgesConnecting(final Set<Node> interestingNodes) {
        final Set<Edge> edges = new LinkedHashSet<>();

        for (final Edge e : this.getEdges()) {
            final Node start = e.getStart();
            final Node end = e.getEnd();
            if (interestingNodes.contains(start) && interestingNodes.contains(end)) {
                edges.add(e);
            }
        }

        return edges;
    }
}
