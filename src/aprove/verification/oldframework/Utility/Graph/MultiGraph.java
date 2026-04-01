package aprove.verification.oldframework.Utility.Graph;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class represents a directed graph with multiple edges between two nodes
 * (implemented as sets of labels). WARNING: This class is only tested for RFC
 * Matchbounds and might be wrong in some parts that are not used there.
 * @author Carsten Otto
 */
public class MultiGraph<N, E> implements java.io.Serializable {

    private static final long serialVersionUID = -1932909372118750524L;

    private int modCount = 0;

    private interface SerializableSet<U> extends Set<U>, Serializable {
    }

    /**
     * The set of nodes of this graph. This set may directly be modified and
     * changes are reflected in the corresponding graph.
     */
    final Set<Node<N>> nodes =

    new SerializableSet<Node<N>>() {

        private static final long serialVersionUID = 1L;

        @Override
        public int size() {
            return MultiGraph.this.out.size();
        }

        @Override
        public boolean isEmpty() {
            return MultiGraph.this.out.isEmpty();
        }

        @Override
        public boolean contains(final Object n) {
            final Node<N> node = (Node) n;
            return MultiGraph.this.out.containsKey(node);
        }

        @Override
        public Iterator<Node<N>> iterator() {

            return new Iterator<Node<N>>() {

                private final Iterator<Map.Entry<Node<N>, CollectionMap<Node<N>, E>>> iter =
                    MultiGraph.this.out.entrySet().iterator();
                private Map.Entry<Node<N>, CollectionMap<Node<N>, E>> lastReturned = null;

                @Override
                public boolean hasNext() {
                    return this.iter.hasNext();
                }

                @Override
                public Node<N> next() {
                    this.lastReturned = this.iter.next();
                    return this.lastReturned.getKey();
                }

                @Override
                public void remove() {
                    if (this.lastReturned == null) {
                        throw new IllegalStateException();
                    }
                    this.iter.remove();
                    MultiGraph.this.removeNode(this.lastReturned.getKey(), this.lastReturned.getValue());
                    this.lastReturned = null;

                }

            };

        }

        @Override
        public Object[] toArray() {
            final int n = this.size();
            final Object[] a = new Object[n];
            int i = 0;
            for (final Node<N> node : this) {
                a[i] = node;
                i++;
            }
            return a;
        }

        @Override
        public <T> T[] toArray(final T[] array) {
            T[] a = array;
            final int n = this.size();
            int m = a.length;
            if (m < n) {
                a = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), n);
                m = n;
            }
            int i = 0;
            final Object[] b = a;
            for (final Node<N> node : this) {
                b[i] = node;
                i++;
            }
            if (m != n) {
                b[i] = null;
            }
            return a;
        }

        @Override
        public boolean add(final Node<N> node) {
            return MultiGraph.this.addNode(node);
        }

        @Override
        public boolean remove(final Object node) {
            return MultiGraph.this.removeNode((Node<N>) node);
        }

        @Override
        public boolean containsAll(final Collection<?> arg0) {
            for (final Object o : arg0) {
                if (!MultiGraph.this.out.containsKey(o)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public boolean addAll(final Collection<? extends Node<N>> nodes) {
            boolean changed = false;
            for (final Node<N> node : nodes) {
                if (MultiGraph.this.addNode(node)) {
                    changed = true;
                }
            }
            return changed;
        }

        @Override
        public boolean retainAll(final Collection<?> set) {

            boolean changed = false;
            final Iterator<Node<N>> it = this.iterator();

            while (it.hasNext()) {
                if (!set.contains(it.next())) {
                    it.remove();
                    changed = true;
                }
            }
            return changed;
        }

        @Override
        public boolean removeAll(final Collection<?> arg0) {
            boolean changed = false;
            for (final Node<N> node : MultiGraph.this.nodes) {
                if (MultiGraph.this.removeNode(node)) {
                    changed = true;
                }
            }
            return changed;
        }

        @Override
        public void clear() {
            throw new IllegalStateException();
        }

        @Override
        public int hashCode() {
            return MultiGraph.this.out.keySet().hashCode();
        }

        @Override
        public boolean equals(final Object o) {
            return MultiGraph.this.out.keySet().equals(o);
        }

        @Override
        public String toString() {
            return MultiGraph.this.out.keySet().toString();
        }

    };

    /**
     * The set of edges of this graph. Changes in the graph are reflected in
     * this set. However, it is (up to now) not possible to change this set like
     * it is possible for the node-set.
     */
    final Set<EdgeEquality<E, N>> edges = new AbstractSet<EdgeEquality<E, N>>() {

        private static final long serialVersionUID = 1L;

        @Override
        public int size() {
            int size = 0;
            for (final CollectionMap<Node<N>, E> value : MultiGraph.this.out.values()) {
                size += value.size();
            }
            return size;
        }

        @Override
        public boolean isEmpty() {
            return MultiGraph.this.out.isEmpty();
        }

        @Override
        @SuppressWarnings("unchecked")
        public boolean contains(final Object o) {
            if (o instanceof EdgeEquality) {
                return this.contains((EdgeEquality<E, N>) o);
            }
            return false;
        }

        public boolean contains(final EdgeEquality<E, N> edge) {
            return MultiGraph.this.contains(edge.startNode, edge.endNode);
        }

        @Override
        public Iterator<EdgeEquality<E, N>> iterator() {

            return new Iterator<EdgeEquality<E, N>>() {
                final Iterator<Map.Entry<Node<N>, CollectionMap<Node<N>, E>>> startNodeIterator =
                    MultiGraph.this.out.entrySet().iterator();
                final int requiredModCount = MultiGraph.this.modCount;

                Node<N> src = null;
                Node<N> dest = null;
                Iterator<Node<N>> endNodeIterator = null;
                boolean nextInvalid = true;
                EdgeEquality<E, N> nextEdge = null;
                CollectionMap<Node<N>, E> nextOut;

                private void computeNext() {
                    if (MultiGraph.this.modCount != this.requiredModCount) { // something changed!
                        throw new ConcurrentModificationException();
                    }
                    while (this.nextInvalid) {
                        if (this.endNodeIterator == null) {
                            if (this.startNodeIterator.hasNext()) {
                                // handle a new node and a new set of edges going out from that node
                                final Map.Entry<Node<N>, CollectionMap<Node<N>, E>> temp =
                                    this.startNodeIterator.next();
                                this.src = temp.getKey();
                                this.nextOut = temp.getValue();
                                this.endNodeIterator = this.nextOut.keySet().iterator();
                            } else {
                                this.nextEdge = null;
                                this.nextInvalid = false;
                            }
                        } else {
                            // we have a node iterator, just handle the edge set from the next node
                            if (this.endNodeIterator.hasNext()) {
                                this.dest = this.endNodeIterator.next();
                                this.nextEdge =
                                    new EdgeEquality<E, N>(this.src, this.dest, this.nextOut.get(this.dest));
                                this.nextInvalid = false;
                            } else {
                                // the node iterator reached it's end, so select a new start node from the startNodeIterator
                                this.endNodeIterator = null;
                            }
                        }
                    }
                }

                @Override
                public boolean hasNext() {
                    this.computeNext();
                    return this.nextEdge != null;
                }

                @Override
                public EdgeEquality<E, N> next() {
                    this.computeNext();
                    if (this.nextEdge == null) {
                        throw new NoSuchElementException();
                    }
                    this.nextInvalid = true;
                    return this.nextEdge;
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }

            };
        }
    };

    /**
     * A mapping from nodes to outgoing edges. These are the real values;
     */
    private final Map<Node<N>, CollectionMap<Node<N>, E>> out;

    /**
     * A mapping from nodes to ingoing edges. These are mirrored values of out.
     * (Used for fast lookup of what incoming edges a node has)
     */
    private final Map<Node<N>, CollectionMap<Node<N>, E>> in;

    /**
     * Create an empty graph.
     */
    public MultiGraph() {
        this.in = new LinkedHashMap<Node<N>, CollectionMap<Node<N>, E>>();
        this.out = new LinkedHashMap<Node<N>, CollectionMap<Node<N>, E>>();
    }

    /**
     * Adds this edge to the graph. In case any of the nodes is not already part
     * of the graph it will be added.
     * @param edge The edge to add.
     * @return true, if a new edge was added
     */
    public boolean addEdge(final EdgeEquality<E, N> edge) {
        return this.addEdge(edge.startNode, edge.endNode, edge.object);
    }

    /**
     * Adds an edge from a given start node to a given end node to this graph,
     * which is labeled by an <code>Object</code>.
     * @param start the <code>Node</code> where the edge starts
     * @param end the <code>Node</code> where the edge ends
     * @param labels an <code>Object</code> associated with this
     * <code>EdgeEquality</code>
     * @return true, if a new edge was added
     */
    public boolean addEdge(final Node<N> start, final Node<N> end, final E label) {
        return this.addEdge(start, end, Collections.singleton(label));
    }

    /**
     * Adds an edge from a given start node to a given end node to this graph,
     * which is labeled by an <code>Object</code>.
     * @param start the <code>Node</code> where the edge starts
     * @param end the <code>Node</code> where the edge ends
     * @param labels an <code>Object</code> associated with this
     * <code>EdgeEquality</code>
     * @return true, if a new edge was added
     */
    public boolean addEdge(final Node<N> start, final Node<N> end, final Collection<E> labels) {

        this.addNode(start);
        this.addNode(end);

        final boolean added = this.out.get(start).add(end, labels);
        final boolean addedCheck = this.in.get(end).add(start, labels);
        assert (added == addedCheck);
        if (added) {
            this.modified();
            return true;
        }
        return false;
    }

    private void modified() {
        this.modCount++;
    }

    /**
     * Adds a node to the graph.
     * @param node The Node to add.
     * @return true iff the node was added (was a new node)
     */
    public boolean addNode(final Node<N> node) {
        if (node == null || this.out.containsKey(node)) {
            return false;
        }
        this.modified();
        this.out.put(node, new CollectionMap<Node<N>, E>());
        this.in.put(node, new CollectionMap<Node<N>, E>());
        return true;

    }

    /**
     * Removes a node from this graph. All edges to and from this node are
     * deleted as well.
     * @param node The node to remove.
     * @return true, iff the node was removed
     */

    public final boolean removeNode(final Node<N> node) {
        final CollectionMap<Node<N>, E> outMap = this.out.remove(node);
        if (outMap == null) {
            return false;
        }
        this.removeNode(node, outMap);
        return true;
    }

    /**
     * removes a node (which must be present), given its corresponding outMap
     * (which must be non-null). This method should be overwritten by
     * subclasses, if they have to delete additional info. The reason for
     * splitting removeNode into two parts is to be able to use the node-set
     * iterators remove method. Otherwise that method would cause an concurrent
     * modification exception!
     * @param node the node to remove, must exist in graph
     * @param outMap the out map of this node, non-null
     */
    void removeNode(final Node<N> node, final CollectionMap<Node<N>, E> outMap) {
        this.modified();
        final Set<Node<N>> outKeySet = outMap.keySet();
        for (final Node<N> otherNode : outKeySet) {
            final boolean deleted = this.in.get(otherNode).remove(node) != null;
            assert (deleted);
        }

        final CollectionMap<Node<N>, E> inMap = this.in.remove(node);
        final Set<Node<N>> removeOut = new LinkedHashSet<Node<N>>();
        for (final Map.Entry<Node<N>, Collection<E>> entryMap : inMap.entrySet()) {
            final Node<N> key = entryMap.getKey();
            removeOut.add(key);
        }
        for (final Node<N> removeMe : removeOut) {
            final boolean removed = this.out.get(removeMe).remove(node) != null;
            assert (removed);
        }
    }

    /**
     * Get all nodes which are children of this node, e.g., which can be reached
     * from this node by one edge. Do not modify the returned set!
     * @param node The <code>Node</code> for which to return its children.
     * @return A set of all children of the given node.
     */
    private Set<Node<N>> getOut(final Node<N> node) {
        return this.out.get(node).keySet();
    }

    /**
     * Get all nodes which are parents of this node, e.g., there are incoming
     * edges to this node from the parents. Do not modify the returned set!
     * @param node The <code>Node</code> for which to return its parents.
     * @return A set of all parents of the given node.
     */
    private Set<Node<N>> getIn(final Node<N> node) {
        return this.in.get(node).keySet();
    }

    /**
     * Determine all nodes reachable from a given set of start nodes.
     *
     * @param start
     *            the start nodes, from which all reachable nodes should be
     *            determined
     * @return all nodes reachable from a node within <code>start</code>. The
     *         returned set may be modified.
     */
    public Set<Node<N>> determineReachableNodes(final Collection<Node<N>> start) {
        return this.determineReachableNodes(start, null);
    }

    /**
     * Determine all nodes reachable from a given set of start nodes.
     *
     * @param start
     *            the start nodes, from which all reachable nodes should be
     *            determined
     * @param filter
     *            a filter which edges may be selected. If you don't need this,
     *            pass null.
     * @return all nodes reachable from a node within <code>start</code>. The
     *         returned set may be modified.
     */
    public Set<Node<N>> determineReachableNodes(final Collection<Node<N>> start, final EdgeFilter<E, N> filter) {

        final Set<Node<N>> result = new LinkedHashSet<Node<N>>(start);
        final Stack<Node<N>> todo = new Stack<Node<N>>();
        for (final Node<N> node : start) {
            todo.push(node);
        }
        while (!todo.isEmpty()) {
            final Node<N> node = todo.pop();
            for (final Entry<Node<N>, Collection<E>> succ : this.out.get(node).entrySet()) {
                final Node<N> target = succ.getKey();
                final Collection<E> outEdges = succ.getValue();
                for (final E e : outEdges) {
                    if ((filter == null) || filter.selectEdge(node, target, e)) {
                        if (result.add(target)) {
                            todo.push(target);
                        }
                        /*
                         * After we've selected one of the edges going from node
                         * to, we don't need to check the rest.
                         */
                        break;
                    }
                }
            }

        }
        return result;
    }

    /**
     * Determine all nodes reaching a given target set of nodes.
     *
     * @param target
     *            the target nodes, for which all reaching nodes should be
     *            determined
     * @return all nodes reaching a node <code>target</code>. The
     *         returned set may be modified.
     */
    public Set<Node<N>> determineReachingNodes(final Collection<Node<N>> target) {
        return this.determineReachingNodes(target, null);
    }

    /**
     * Determine all nodes reachable from a given set of start nodes.
     *
     * @param target
     *            the target nodes, for which all reaching nodes should be
     *            determined
     * @param filter
     *            a filter which edges may be selected. If you don't need this,
     *            pass null.
     * @return all nodes reaching a node <code>target</code>. The
     *         returned set may be modified.
     */
    public Set<Node<N>> determineReachingNodes(final Collection<Node<N>> target, final EdgeFilter<E, N> filter) {

        final Set<Node<N>> result = new LinkedHashSet<Node<N>>(target);
        final Stack<Node<N>> todo = new Stack<Node<N>>();
        for (final Node<N> node : target) {
            todo.push(node);
        }
        while (!todo.isEmpty()) {
            final Node<N> node = todo.pop();
            for (final Entry<Node<N>, Collection<E>> pred : this.in.get(node).entrySet()) {
                final Node<N> source = pred.getKey();
                final Collection<E> inEdges = pred.getValue();
                for (final E e : inEdges) {
                    if ((filter == null) || filter.selectEdge(source, node, e)) {
                        if (result.add(source)) {
                            todo.push(source);
                        }
                        /*
                         * After we've selected one of the edges going from node
                         * to, we don't need to check the rest.
                         */
                        break;
                    }
                }
            }

        }
        return result;
    }

    /**
     * Checks whether the graph contains an edge from start to end
     */
    public boolean contains(final Node<N> start, final Node<N> end) {

        final CollectionMap<Node<N>, E> out = this.out.get(start);
        if (out == null) {
            return false;
        }
        return out.containsKey(end);
    }

    /**
     * Checks whether the graph contains a given node.
     * @param node Node to check for.
     * @return True if the graph contains such a node.
     */
    public boolean contains(final Node<N> node) {
        return this.out.containsKey(node);
    }

    /**
     * Checks if thew given graph is equal to this graph. This is not a check
     * for isomorphism.
     * @param obj Graph to check equality on.
     * @return True if the graphs are equal.
     */
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
        final MultiGraph other = (MultiGraph) obj;
        if (this.out == null) {
            if (other.out != null) {
                return false;
            }
        } else if (!this.out.equals(other.out)) {
            return false;
        }
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.out == null) ? 0 : this.out.hashCode());
        return result;
    }

    /**
     * Checks whether the graph contains a path from start to end.
     * <P>
     * Note: There is always a path (of length 0) from a node to itself, even if
     * there is no such edge.
     * @param start Start node of the path.
     * @param end End node of the path.
     * @return <code>true</code> if the graph contains such a path,
     * <code>false</code> otherwise
     */
    public boolean hasPath(final Node<N> start, final Node<N> end) {
        return this.hasPath(start, end, true, null);
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
     *  means "every edge is allowed")
     * @return <code>true</code> if the graph contains such a path,
     * <code>false</code> otherwise
     */
    public boolean hasPath(final Node<N> start,
        final Node<N> end,
        final boolean allowEmptyPaths,
        final EdgeFilter<E, N> filter) {

        if (Globals.useAssertions) {
            assert (start != null && end != null);
        }

        final Set<Node<N>> done = new HashSet<Node<N>>();
        final Stack<Node<N>> todo = new Stack<Node<N>>();

        if (allowEmptyPaths) {
            todo.push(start);
            done.add(start);
        } else {
            for (final Entry<Node<N>, Collection<E>> outEdgesToTarget : this.out.get(start).entrySet()) {
                final Node<N> target = outEdgesToTarget.getKey();
                done.add(target);
                todo.push(target);
            }
        }

        while (!todo.isEmpty()) {
            final Node<N> node = todo.pop();
            if (node.equals(end)) {
                return true;
            }
            for (final Entry<Node<N>, Collection<E>> outEdgesToTarget : this.out.get(node).entrySet()) {
                final Node<N> target = outEdgesToTarget.getKey();
                edges: for (final E outEdge : outEdgesToTarget.getValue()) {
                    if (filter == null || filter.selectEdge(node, target, outEdge)) {
                        if (done.add(target)) {
                            todo.push(target);
                            break edges;
                        }
                    }
                }
            }
        }

        return false;

    }

    /**
     * Returns a shortest path between <code>start</code> and <code>end</code>
     * if there exists one.
     * @param start Start node of the path.
     * @param end End node of the path.
     * @return a list of nodes making up a path in this graph, with
     * <code>start</code> as first and <code>end</code> as last element. If no
     * path exists, the <code>null</code> pointer is returned.
     */
    public LinkedList<Node<N>> getPath(final Node<N> start, final Node<N> end) {
        if (Globals.useAssertions) {
            assert (start != null && end != null);
        }

        final Map<Node<N>, Node<N>> reachedOver = new HashMap<Node<N>, Node<N>>();
        reachedOver.put(start, null);

        final Stack<Node<N>> todo = new Stack<Node<N>>();
        todo.push(start);

        while (!todo.isEmpty()) {
            final Node<N> node = todo.pop();
            if (node.equals(end)) {
                final LinkedList<Node<N>> res = new LinkedList<Node<N>>();
                res.add(node);
                Node<N> pred = reachedOver.get(node);
                while (pred != null) {
                    res.addFirst(pred);
                    pred = reachedOver.get(pred);
                }
                return res;
            }
            for (final Node<N> succ : this.out.get(node).keySet()) {
                if (!reachedOver.containsKey(succ)) {
                    reachedOver.put(succ, node);
                    todo.push(succ);
                }
            }
        }

        return null;
    }

    /**
     * Returns edges on the shortest path between <code>start</code> and
     * <code>end</code> if there exists one.
     * @param start Start node of the path.
     * @param end End node of the path.
     * @return a list of nodes edges up a path in this graph, with
     * <code>start</code> as start of the first edge and <code>end</code> as
     * target of the last element. If no path exists, the <code>null</code>
     * pointer is returned.
     */
    public LinkedList<E> getEdgesOnPath(final Node<N> start, final Node<N> end) {
        return this.getEdgesOnPath(start, end, true, null);
    }

    /**
     * Returns edges on the shortest path between <code>start</code> and
     * <code>end</code> if there exists one.
     * @param start Start node of the path.
     * @param end End node of the path.
     * @param filter a filter deciding which edges may be selected (may be null,
     *  means "every edge is allowed")
     * @return a list of nodes edges up a path in this graph, with
     * <code>start</code> as start of the first edge and <code>end</code> as
     * target of the last element. If no path exists, the <code>null</code>
     * pointer is returned.
     */
    public LinkedList<E> getEdgesOnPath(final Node<N> start, final Node<N> end, final EdgeFilter<E, N> filter) {
        return this.getEdgesOnPath(start, end, true, null);
    }

    /**
     * Returns edges on the shortest path between <code>start</code> and
     * <code>end</code> if there exists one.
     * @param start Start node of the path.
     * @param end End node of the path.
     * @param allowEmptyPaths if true, an empty path is allowed.
     * @param filter a filter deciding which edges may be selected (may be null,
     *  means "every edge is allowed")
     * @return a list of nodes edges up a path in this graph, with
     * <code>start</code> as start of the first edge and <code>end</code> as
     * target of the last element. If no path exists, the <code>null</code>
     * pointer is returned.
     */
    public LinkedList<E> getEdgesOnPath(final Node<N> start,
        final Node<N> end,
        final boolean allowEmptyPaths,
        final EdgeFilter<E, N> filter) {
        if (Globals.useAssertions) {
            assert (start != null && end != null);
        }

        final Map<Node<N>, Node<N>> reachedOver = new HashMap<Node<N>, Node<N>>();
        reachedOver.put(start, null);
        final Map<Pair<Node<N>, Node<N>>, E> connectedBy = new HashMap<Pair<Node<N>, Node<N>>, E>();

        final Stack<Node<N>> todo = new Stack<Node<N>>();
        if (allowEmptyPaths) {
            todo.push(start);
        } else {
            for (final Entry<Node<N>, Collection<E>> outEdgesToTarget : this.out.get(start).entrySet()) {
                final Node<N> target = outEdgesToTarget.getKey();
                edges: for (final E outEdge : outEdgesToTarget.getValue()) {
                    if (filter == null || filter.selectEdge(start, target, outEdge)) {
                        reachedOver.put(target, start);
                        connectedBy.put(new Pair<Node<N>, Node<N>>(start, target), outEdge);
                        todo.push(target);
                        break edges;
                    }
                }
            }
        }

        while (!todo.isEmpty()) {
            final Node<N> node = todo.pop();
            if (node.equals(end)) {
                final LinkedList<E> res = new LinkedList<E>();
                Node<N> cur = end;
                do {
                    final Node<N> pred = reachedOver.get(cur);
                    res.addFirst(connectedBy.get(new Pair<Node<N>, Node<N>>(pred, cur)));
                    cur = pred;
                } while (cur != null && cur != start);
                return res;
            }

            for (final Entry<Node<N>, Collection<E>> outEdgesToTarget : this.out.get(node).entrySet()) {
                final Node<N> target = outEdgesToTarget.getKey();
                edges: for (final E outEdge : outEdgesToTarget.getValue()) {
                    if (filter == null || filter.selectEdge(node, target, outEdge)) {
                        if (!reachedOver.containsKey(target) || reachedOver.get(target) == null) {
                            connectedBy.put(new Pair<Node<N>, Node<N>>(node, target), outEdge);
                            todo.push(target);
                            reachedOver.put(target, node);
                        }

                        break edges;
                    }
                }
            }
        }

        return null;
    }

    /**
     * Gets all edges ending in a specified node
     * @param node the <code>Node</code>, of which all entering edges should be
     * determined, this node must be present in the graph.
     * @return all edges ending in <code>node</code>
     */
    public Set<EdgeEquality<E, N>> getInEdges(final Node<N> dest) {
        if (Globals.useAssertions) {
            assert (this.out.containsKey(dest));
        }

        final CollectionMap<Node<N>, E> theInMap = this.in.get(dest);

        return new AbstractSet<EdgeEquality<E, N>>() {

            private static final long serialVersionUID = 1L;

            @Override
            public int size() {
                return theInMap.keySet().size();
            }

            @Override
            public boolean isEmpty() {
                return theInMap.isEmpty();
            }

            @Override
            public boolean contains(final Object e) {
                final EdgeEquality<E, N> edge = (EdgeEquality) e;
                if (edge.endNode.equals(dest)) {
                    if (theInMap.containsKey(edge.startNode)) {
                        return theInMap.get(edge.startNode).contains(edge.object);
                    }
                    return false;
                }
                return false;
            }

            @Override
            public Iterator<EdgeEquality<E, N>> iterator() {

                return new Iterator<EdgeEquality<E, N>>() {

                    final Iterator<Map.Entry<Node<N>, Collection<E>>> inMapIter = theInMap.entrySet().iterator();

                    @Override
                    public boolean hasNext() {
                        return this.inMapIter.hasNext();
                    }

                    @Override
                    public EdgeEquality<E, N> next() {
                        if (this.inMapIter.hasNext()) {
                            final Map.Entry<Node<N>, Collection<E>> srcmap = this.inMapIter.next();
                            return new EdgeEquality<E, N>(srcmap.getKey(), dest, srcmap.getValue());
                        }
                        return null;
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }

                };

            }

        };

    }

    /**
     * Gets all edges starting at a specified node
     * @param node the <code>Node</code>, from which all leaving edges should be
     * determined, this node must be present in the graph.
     * @return all edges leaving <code>node</code> as keys and the values are
     * the labels
     */
    public Set<EdgeEquality<E, N>> getOutEdges(final Node<N> src) {

        if (Globals.useAssertions) {
            assert (this.out.containsKey(src));
        }

        final CollectionMap<Node<N>, E> theOutMap = this.out.get(src);

        return new AbstractSet<EdgeEquality<E, N>>() {

            private static final long serialVersionUID = 1L;

            @Override
            public int size() {
                return theOutMap.keySet().size();
            }

            @Override
            public boolean isEmpty() {
                return theOutMap.isEmpty();
            }

            @Override
            public boolean contains(final Object e) {
                final EdgeEquality<E, N> edge = (EdgeEquality) e;
                if (edge.startNode.equals(src)) {
                    return theOutMap.containsKey(edge.endNode) && theOutMap.get(edge.endNode).containsAll(edge.object)
                        && edge.object.containsAll(theOutMap.get(edge.endNode));
                }
                return false;
            }

            @Override
            public Iterator<EdgeEquality<E, N>> iterator() {
                final Iterator<Map.Entry<Node<N>, Collection<E>>> outMapIter = theOutMap.entrySet().iterator();

                return new Iterator<EdgeEquality<E, N>>() {

                    @Override
                    public boolean hasNext() {
                        return outMapIter.hasNext();
                    }

                    @Override
                    public EdgeEquality<E, N> next() {
                        final Map.Entry<Node<N>, Collection<E>> destmap = outMapIter.next();
                        final Node<N> dest = destmap.getKey();
                        return new EdgeEquality<E, N>(src, dest, destmap.getValue());
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }

                };

            }

        };
    }

    /**
     * Returns the set of edges of this graph. The returned set cannot be
     * modified. However, changes in the graph will be reflected in this set.
     * @return The set of edges of this graph.
     */
    public Set<EdgeEquality<E, N>> getEdges() {
        return this.edges;
    }

    /**
     * Return the edge between two given nodes.
     * @return The edge between two given nodes, if it exists, null otherwise.
     */

    public EdgeEquality<E, N> getEdge(final Node<N> start, final Node<N> end) {
        final CollectionMap<Node<N>, E> out = this.out.get(start);

        if (out != null && out.containsKey(end)) {
            return new EdgeEquality<E, N>(start, end, out.get(end));
        }
        return null;
    }

    /**
     * Returns the set of nodes of this graph. Note that all changes in this set
     * will be reflected in this graph and vice versa.
     * @return The set of nodes of this graph.
     */

    public Set<Node<N>> getNodes() {
        return this.nodes;
    }

    /**
     * Overwrites the <code>toString</code> method of <code>Object</code>
     * @return a <code>String</code> representing this object
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("Nodes:\n");
        sb.append(this.nodes.toString());
        sb.append("\nEdges:\n");
        for (final EdgeEquality<E, N> edge : this.edges) {
            sb.append(edge.getStartNode().getNodeNumber());
            sb.append(" -> ");
            sb.append(edge.getEndNode().getNodeNumber());
            sb.append(": ");
            sb.append(edge.getObject());
            sb.append("\n");
        }
        return sb.toString();
    }

    /**
     * Checks whether an <code>Object</code> implements the
     * <code>PrettyStringable</code> interface. If so, its method is invoked
     * and the resulting String is returned, otherwise, the
     * <code>toString</code>-result of the object is returned.
     * @param obj the <code>Object</code> to check for
     * <code>PrettyStringable</code>
     * @return the result of <code>prettyToString</code> or
     * <code>toString</code>, depending if the object implements the
     * <code>PrettyStringable</code> interface or not
     */
    public String getPrettyString(final Object obj) {
        if (obj != null) {
            return obj instanceof PrettyStringable ? ((PrettyStringable) obj).prettyToString() : obj.toString();
        }
        return "NULL";
    }

    /**
     * This method is used to save a graph in nice dot format without node
     * numbers. Additional, it labels the edges by using the toString() method
     * of the objects stored in the edges.
     */

    public String toSaveDOTwithEdges() {

        final StringBuffer t = new StringBuffer("");
        t.append("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        final Iterator<Node<N>> i = this.nodes.iterator();
        while (i.hasNext()) {
            final Node<N> from = i.next();
            Set<Node<N>> out = this.getOut(from);
            if (out == null) {
                out = new HashSet<Node<N>>();
            }
            t.append(from.getNodeNumber() + " [");
            if (from.object != null) {
                t.append("label=\"" + this.getPrettyString(from.object) + "\", ");
            }
            t.append("fontsize=16");
            t.append("];\n");
            final Iterator<Node<N>> j = out.iterator();
            if (!j.hasNext()) {
                continue;
            }

            while (j.hasNext()) {
                final Node<N> to = j.next();
                final EdgeEquality<E, N> edge = this.getEdge(from, to);
                if (!this.edges.isEmpty()) {
                    t.append(from.getNodeNumber() + " -> {");
                    t.append(to.getNodeNumber() + "} ");
                    t.append("[label = \"");
                    if (edge.object == null) {
                        t.append("null");
                    } else {
                        t.append(this.getPrettyString(edge.object));
                    }
                    t.append("\"];\n");
                }
            }
        }

        return t.toString() + "}\n";

    }

    /**
     * This method is used to save a graph in nice dot format without node
     * numbers. Additional, it labels the edges by using the toString() method
     * of the objects stored in the edges.
     */

    public String toInteractiveDOTwithEdges() {

        final StringBuffer t = new StringBuffer("");
        t.append("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        int maxNodeNr = 0;
        for (final Node<N> from : this.nodes) {
            final int nr = from.getNodeNumber();
            if (nr > maxNodeNr) {
                maxNodeNr = nr;
            }
            t.append(nr + " [");
            if (from.object != null) {
                t.append("label=\"" + this.getPrettyString(from.object) + "\", ");
            }
            t.append("fontsize=10");
            t.append("];\n");
        }

        for (final EdgeEquality<E, N> edge : this.getEdges()) {
            maxNodeNr++;
            t.append(maxNodeNr + " [label=\"" + this.getPrettyString(edge.getObject())
                + "\", fontsize=16, style = filled, fillcolor = yellow];\n");
            t.append(edge.getStartNode().getNodeNumber() + " -> " + maxNodeNr + " [arrowhead = none];\n");
            t.append(maxNodeNr + " -> " + edge.getEndNode().getNodeNumber() + ";\n\n");
        }

        return t.toString() + "}\n";

    }

    /**
     * provides a basic implementation of unchangeable sets which just mirror
     * the state of the graph. Moreover, hashes are cached and respect the
     * modification of the graph.
     */
    private abstract class AbstractSet<U> implements SerializableSet<U> {

        private int hashCode;
        private int lastHashCalculation;

        public AbstractSet() {
            this.hashCode = 0;
            this.lastHashCalculation = MultiGraph.this.modCount - 1;
        }

        @Override
        public Object[] toArray() {
            final int n = this.size();
            final Object[] a = new Object[n];
            int i = 0;
            for (final U u : this) {
                a[i] = u;
                i++;
            }
            return a;
        }

        @Override
        public <T> T[] toArray(T[] a) {
            final int n = this.size();
            int m = a.length;
            if (m < n) {
                a = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), n);
                m = n;
            }
            int i = 0;
            final Object[] b = a;
            for (final U u : this) {
                b[i] = u;
                i++;
            }
            if (m != n) {
                b[i] = null;
            }
            return a;
        }

        @Override
        public boolean add(final U arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean remove(final Object arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean containsAll(final Collection<?> arg) {
            for (final Object edge : arg) {
                if (!this.contains(edge)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public boolean addAll(final Collection<? extends U> arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean retainAll(final Collection<?> arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean removeAll(final Collection<?> arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void clear() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String toString() {
            final StringBuffer buf = new StringBuffer();
            boolean first = true;
            for (final U elem : this) {
                if (first) {
                    buf.append("{");
                    first = false;
                } else {
                    buf.append(", ");
                }
                buf.append(elem);
            }
            if (first) {
                buf.append("empty set");
            } else {
                buf.append("}");
            }
            return buf.toString();
        }

        @Override
        public int hashCode() {
            while (this.lastHashCalculation != MultiGraph.this.modCount) {
                this.lastHashCalculation = MultiGraph.this.modCount;
                int hash = 0;
                for (final U elem : this) {
                    hash += elem.hashCode();
                }
                this.hashCode = hash;
            }
            return this.hashCode;
        }

        @Override
        public boolean equals(final Object o) {
            final Set other = (Set) o;
            if (this.size() == other.size()) {
                return this.containsAll(other);
            }
            return false;
        }

    }

    public void removeEdges(final Node<N> start, final Node<N> end, final Collection<E> delEdges) {
        if (delEdges.isEmpty()) {
            return;
        }
        final Set<E> copy = new LinkedHashSet<E>(delEdges);
        final Collection<E> coll1 = this.out.get(start).get(end);
        coll1.removeAll(copy);
        if (coll1.isEmpty()) {
            this.out.get(start).remove(end);
        }
        final Collection<E> coll2 = this.in.get(end).get(start);
        coll2.removeAll(copy);
        if (coll2.isEmpty()) {
            this.in.get(end).remove(start);
        }
    }

    /**
     * Computes the set of SCCs in the following order: if a SCC is returned
     * before another, then from the first SCC there is no path to the later
     * SCC. If the parameter is set, the result will also contain nodes that are
     * reached more than once during SCC computation.
     * @param computeInterestingNodes if true, also return the interesting nodes
     * @return the SCCs in this graph, if wished inclusing information about
     * interesting nodes
     */
    public LinkedHashSet<Cycle<N>> getSCCsWithInterestingNodes(final boolean computeInterestingNodes) {
        return this.getSCCsWithInterestingNodes(computeInterestingNodes, null);
    }

    /**
     * Computes the set of SCCs in the following order: if a SCC is returned
     * before another, then from the first SCC there is no path to the later
     * SCC. If the parameter is set, the result will also contain nodes that are
     * reached more than once during SCC computation.
     * @param computeInterestingNodes if true, also return the interesting nodes
     * @param filter only regard edges this filter allows (null: all)
     * @return the SCCs in this graph, if wished inclusing information about
     * interesting nodes
     */
    public LinkedHashSet<Cycle<N>> getSCCsWithInterestingNodes(final boolean computeInterestingNodes,
        final EdgeFilter<Collection<E>, N> filter) {
        int n = this.nodes.size();
        final HashSet<Node<N>> visitedNodes = new HashSet<Node<N>>(n);
        final List<Node<N>> sortedNodes = new ArrayList<Node<N>>(n);
        Collection<Node<N>> interestingNodes = null;
        if (computeInterestingNodes) {
            interestingNodes = new LinkedHashSet<Node<N>>();
        }
        for (final Node<N> node : this.nodes) {
            this.visitFirst(node, visitedNodes, sortedNodes, interestingNodes, filter);
        }
        Collection<Node<N>> reallyInterestingNodes = null;
        if (computeInterestingNodes) {
            assert (interestingNodes != null);
            reallyInterestingNodes = new LinkedHashSet<Node<N>>();
            if (visitedNodes.size() > 4) {
                for (final Node<N> interestingNode : interestingNodes) {
                    final int sizeIn = this.getIn(interestingNode).size();
                    if (sizeIn <= 1) {
                        continue;
                    }
                    final int sizeOut = this.getOut(interestingNode).size();
                    if (sizeOut <= 1) {
                        continue;
                    }
                    reallyInterestingNodes.add(interestingNode);
                }
            }
        }
        // okay, now traverse in reverse order to compute Sccs
        visitedNodes.clear();
        final LinkedHashSet<Cycle<N>> allSccs = new LinkedHashSet<Cycle<N>>();
        while (n != 0) {
            n--;
            final Node<N> node = sortedNodes.get(n);
            if (visitedNodes.contains(node)) {
                // we already visited this node
                continue;
            }
            final Cycle<N> currentScc = new Cycle<N>();
            for (final Entry<Node<N>, Collection<E>> entry : this.out.get(node).entrySet()) {
                final Node<N> outNode = entry.getKey();
                if (filter == null) {
                    this.visitSecond(outNode, currentScc, visitedNodes, reallyInterestingNodes, null);
                } else {
                    if (filter.selectEdge(node, outNode, entry.getValue())) {
                        this.visitSecond(outNode, currentScc, visitedNodes, reallyInterestingNodes, filter);
                    }
                }
            }
            if (!visitedNodes.add(node)) {
                allSccs.add(currentScc);
            }

        }
        return allSccs;
    }

    /**
     * Computes the set of SCCs in the following order: if a SCC is returned
     * before another, then from the first SCC there is no path to the later SCC
     * @return the SCCs in this graph
     */
    public LinkedHashSet<Cycle<N>> getSCCs() {
        return this.getSCCsWithInterestingNodes(false, null);
    }

    /**
     * Computes the set of SCCs in the following order: if a SCC is returned
     * before another, then from the first SCC there is no path to the later SCC
     * @param filter only regard edges that this filter allows
     * @return the SCCs in this graph
     */
    public LinkedHashSet<Cycle<N>> getSCCs(final EdgeFilter<Collection<E>, N> filter) {
        return this.getSCCsWithInterestingNodes(false, filter);
    }

    /**
     * Visit and mark all nodes of the graph. Start with the given node and
     * follow the incoming edges in a depth-first manner. Collect the visited
     * nodes in correct order in "collect". If a node is visited more than once,
     * it is collected in "interestingNodes" (if not null).
     * @param node the current node
     * @param visited all visited nodes
     * @param collect visited nodes will be collected here
     * @param interestingNodes of not null: will be filled with the nodes that
     * are visited more than once
     * @param filter only visit the edges the filter allowes (null: all edges)
     * @return false iff we reached an already visited node
     */
    private boolean visitFirst(final Node<N> node,
        final Set<Node<N>> visited,
        final List<Node<N>> collect,
        final Collection<Node<N>> interestingNodes,
        final EdgeFilter<Collection<E>, N> filter) {
        if (visited.add(node)) {
            for (final Entry<Node<N>, Collection<E>> entry : this.in.get(node).entrySet()) {
                final Node<N> inNode = entry.getKey();
                if (filter == null) {
                    if (!this.visitFirst(inNode, visited, collect, interestingNodes, filter)
                        && interestingNodes != null) {
                        interestingNodes.add(inNode);
                    }
                } else {
                    if (filter.selectEdge(inNode, node, entry.getValue())) {
                        if (!this.visitFirst(inNode, visited, collect, interestingNodes, filter)
                            && interestingNodes != null) {
                            interestingNodes.add(inNode);
                        }
                    }
                }
            }
            collect.add(node);
            return true;
        }
        return false;
    }

    private void visitSecond(final Node<N> node,
        final Cycle<N> currentScc,
        final Set<Node<N>> visited,
        final Collection<Node<N>> interestingNodes,
        final EdgeFilter<Collection<E>, N> filter) {
        if (visited.add(node)) {
            if (interestingNodes != null && interestingNodes.contains(node)) {
                currentScc.addInteresting(node);
            } else {
                currentScc.add(node);
            }
            for (final Entry<Node<N>, Collection<E>> entry : this.out.get(node).entrySet()) {
                final Node<N> outNode = entry.getKey();
                if (filter == null) {
                    this.visitSecond(outNode, currentScc, visited, interestingNodes, null);
                } else {
                    if (filter.selectEdge(node, outNode, entry.getValue())) {
                        this.visitSecond(outNode, currentScc, visited, interestingNodes, filter);
                    }
                }
            }
        }
    }

    /**
     * Creates a (sub-)graph consisting only of the given nodes and the
     * connections between them according to this graph.
     */
    public MultiGraph<N, E> getSubGraph(final Set<Node<N>> newNodes) {
        return new MultiGraph<N, E>(newNodes, this);
    }

    /**
     * Creates a (sub-)graph consisting only of the given nodes and the
     * connections between them according to a given graph.
     */
    public MultiGraph(final Set<Node<N>> nodes, final MultiGraph<N, E> graph) {
        this(nodes);
        for (final Node<N> src : nodes) {
            final CollectionMap<Node<N>, E> newEdges = graph.out.get(src);
            // check whether src node is in nodes
            if (newEdges != null) {
                for (final Map.Entry<Node<N>, Collection<E>> edge : newEdges.entrySet()) {
                    final Node<N> dest = edge.getKey();
                    // if dest node is also in nodes, then add the edge
                    if (nodes.contains(dest)) {
                        this.addEdge(src, dest, edge.getValue());
                    }
                }
            }
        }
    }

    /**
     * Creates a graph from the given set of nodes. That graph will not contain
     * any edges yet.
     * @param nodes The set of nodes for the new graph.
     */
    public MultiGraph(final Set<Node<N>> nodes) {
        this(nodes, new LinkedHashSet<EdgeEquality<E, N>>());
    }

    /**
     * Creates a graph from the given set of nodes and edges.
     * @param nodes The set of nodes for the new graph.
     * @param edges The set of edges the new graph should contain.
     */
    public MultiGraph(final Set<Node<N>> nodes, final Set<EdgeEquality<E, N>> edges) {
        final int n = nodes.size();

        this.in = new LinkedHashMap<Node<N>, CollectionMap<Node<N>, E>>(n);
        this.out = new LinkedHashMap<Node<N>, CollectionMap<Node<N>, E>>(n);
        for (final Node<N> node : nodes) {
            this.addNode(node);
        }
        for (final EdgeEquality<E, N> edge : edges) {
            this.addEdge(edge.startNode, edge.endNode, edge.object);
        }
        this.modCount = 1;
    }
}
