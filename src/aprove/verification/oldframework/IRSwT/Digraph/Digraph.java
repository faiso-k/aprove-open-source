package aprove.verification.oldframework.IRSwT.Digraph;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Represents a directed graph. Two nodes u,v of a digraph
 * can be connected by an edge (u,v) or not. Loops from a node
 * u to u itself are also allowed.
 * This graph is mutable, so be careful!
 *
 * @author Matthias Hoelzel
 * @param <V> vertex type, should be hashable.
 */
public class Digraph<V> implements Exportable {
    /** The vertices of this graph. */
    private final LinkedHashSet<V> vertices;

    /** Set of edges. */
    private final LinkedHashSet<Pair<V, V>> edges;

    /** Stores the neighbors of given node. */
    private final LinkedHashMap<V, LinkedHashSet<V>> neighbors;

    /** Stores the neighbors of the inverted graph (where the direction of each edge is flipped). */
    private final LinkedHashMap<V, LinkedHashSet<V>> invertedNeighbors;

    /** If true, then this digraph cannot be changed anymore! */
    private boolean frozen;

    /**
     * Create an empty Digraph.
     */
    public Digraph() {
        this.vertices = new LinkedHashSet<>();
        this.edges = new LinkedHashSet<>();
        this.neighbors = new LinkedHashMap<>();
        this.invertedNeighbors = new LinkedHashMap<>();
    }

    /**
     * Create a new directed graph.
     * @param initialVertices initial vertices
     * @param initialEdges edges to start with. edges from or to nodes which
     * are not in the set of initial vertices are ignored!
     */
    public Digraph(final Collection<V> initialVertices, final Collection<Pair<V, V>> initialEdges) {
        this.vertices = new LinkedHashSet<>(initialVertices);
        this.edges = new LinkedHashSet<>(initialEdges);
        this.neighbors = new LinkedHashMap<>();
        this.invertedNeighbors = new LinkedHashMap<>();
        for (final V v : this.vertices) {
            assert v != null : "Dont like null!";
            this.neighbors.put(v, new LinkedHashSet<V>());
            this.invertedNeighbors.put(v, new LinkedHashSet<V>());
        }
        for (final Pair<V, V> e : this.edges) {
            assert e != null && e.x != null && e.y != null : "Dont like null!";
            if (!this.vertices.contains(e.x) || !this.vertices.contains(e.y)) {
                continue;
            }
            this.neighbors.get(e.x).add(e.y);
            this.invertedNeighbors.get(e.y).add(e.x);
        }
    }

    /**
     * Creates a copy of this. Useful for creating a copy of a frozen digraph,
     * that can be modified again.
     * @param dig some directed graph
     */
    public Digraph(final Digraph<V> dig) {
        this(dig.vertices, dig.edges);
    }

    /**
     * Adds a new vertex.
     * If frozen, then we throw an error.
     * @param v vertex you want to add
     */
    public void addVertex(final V v) {
        if (this.frozen) {
            throw new UnsupportedOperationException("Cannot modify frozen data structur!");
        }
        assert v != null : "Dont like null!";
        this.vertices.add(v);
        if (!this.neighbors.containsKey(v)) {
            this.neighbors.put(v, new LinkedHashSet<V>());
        }
        if (!this.invertedNeighbors.containsKey(v)) {
            this.invertedNeighbors.put(v, new LinkedHashSet<V>());
        }
    }

    /**
     * Adds a new vertex.
     * If frozen, then we throw an error.
     * @param v vertex you want to add
     */
    public void removeVertex(final V v) {
        if (this.frozen) {
            throw new UnsupportedOperationException("Cannot modify frozen data structur!");
        }
        assert v != null : "Dont like null!";
        if (!this.vertices.contains(v)) {
            return;
        }
        this.vertices.remove(v);
        this.edges.remove(new Pair<V, V>(v, v));
        this.neighbors.get(v).remove(v);
        this.invertedNeighbors.get(v).remove(v);

        for (final V u : this.neighbors.get(v)) {
            final LinkedHashSet<V> invNgbs = this.invertedNeighbors.get(u);
            assert invNgbs.contains(v) : "Inconsistent inverted neighbor sets!";
            this.edges.remove(new Pair<V, V>(v, u));
            invNgbs.remove(v);
        }
        for (final V u : this.invertedNeighbors.get(v)) {
            final LinkedHashSet<V> ngbs = this.neighbors.get(u);
            assert ngbs.contains(v) : "Inconsistent neighbor sets!";
            this.edges.remove(new Pair<V, V>(v, u));
            ngbs.remove(v);
        }
        this.vertices.remove(v);
    }

    /**
     * Adds a new vertex.
     * If frozen, then we throw an error.
     * @param u vertex where you start
     * @param v vertex where you want to end
     */
    public void connect(final V u, final V v) {
        if (this.frozen) {
            throw new UnsupportedOperationException("Cannot modify frozen data structur!");
        }
        assert u != null && v != null : "Dont like null!";
        this.addVertex(v);
        this.addVertex(u);
        this.edges.add(new Pair<>(u, v));
        this.neighbors.get(u).add(v);
        this.invertedNeighbors.get(v).add(u);
    }

    /**
     * Removes the edge again.
     * If frozen, then we throw an error.
     * @param u vertex where you start
     * @param v vertex where you end
     */
    public void disconnect(final V u, final V v) {
        if (this.frozen) {
            throw new UnsupportedOperationException("Cannot modify frozen data structur!");
        }
        assert v != null && u != null : "Dont like null!";
        this.addVertex(u);
        this.addVertex(v);
        this.edges.remove(new Pair<>(u, v));
        this.neighbors.get(u).remove(v);
        this.invertedNeighbors.get(v).remove(u);
    }

    /**
     * Makes this data structure immutable.
     */
    public void freeze() {
        this.frozen = true;
    }

    /**
     * Returns false, iff this data structure can be modified.
     * @return boolean
     */
    public boolean isFrozen() {
        return this.frozen;
    }

    /**
     * Returns true, iff this digraph contains at least one arc.
     * @return boolean
     */
    public boolean hasEdges() {
        return !this.edges.isEmpty();
    }

    /**
     * Returns true whenever there is a edges from u to v.
     * @param u vertex where you start
     * @param v vertex where you end
     * @return boolean
     */
    public boolean isConnected(final V u, final V v) {
        return this.edges.contains(new Pair<>(u, v));
    }

    /**
     * Getter for the set of vertices.
     * @return set of vertices
     */
    public Set<V> getVertices() {
        return Collections.unmodifiableSet(this.vertices);
    }

    /**
     * Getter for the set of edges.
     * @return set of vertices
     */
    public Set<Pair<V, V>> getEdges() {
        return Collections.unmodifiableSet(this.edges);
    }

    /**
     * Returns the set of vertices which can be reached via an edge from v.
     * @param v starting vertex
     * @return set of vertices
     */
    public Set<V> getNeighbors(final V v) {
        return Collections.unmodifiableSet(this.neighbors.get(v));
    }

    /**
     * Returns the set of vertices which have a edge leading to v.
     * @param v some vertex
     * @return set of vertices
     */
    public Set<V> getInvertedNeighbors(final V v) {
        return Collections.unmodifiableSet(this.invertedNeighbors.get(v));
    }

    /**
     * Returns the graph which in induced by a given set of vertics.
     * @param newVertices set of vertices
     * @return an induced subgraph
     */
    public Digraph<V> getInducedSubgraph(final Set<V> newVertices) {
        return new Digraph<>(newVertices, this.edges);
    }

    /**
     * Returns true, iff this graph is fully evaluated.
     * @return boolean
     */
    public boolean isFullyEvaluated() {
        return true;
    }

    /**
     * Returns true iff this digraph consists only of trivial SCCs.
     * @return boolean
     */
    public boolean hasOnlyTrivialSCCs() {
        for (final Set<V> scc : this.getSCCs()) {
            if (Globals.DEBUG_MATTHIAS) {
                System.err.println("Checking SCC: " + scc);
            }
            final Digraph<V> subdigraph = this.getInducedSubgraph(scc);
            if (subdigraph.hasEdges()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Calculates the SCCs.
     * @return list of sets of vertices
     */
    public List<Set<V>> getSCCs() {
        final LinkedList<Set<V>> result = new LinkedList<>();

        // 1. Build stack:
        final LinkedHashSet<V> seen = new LinkedHashSet<>();
        final LinkedList<V> stack = new LinkedList<>();
        for (final V v : this.vertices) {
            if (!seen.contains(v)) {
                this.dfs(v, seen, stack, this.neighbors);
            }
        }

        // 2. Collect SCCs:
        final LinkedHashSet<V> visited = new LinkedHashSet<>();
        while (!stack.isEmpty()) {
            final V v = stack.pop();
            if (!visited.contains(v)) {
                final LinkedList<V> nextSCC = new LinkedList<>();
                this.dfs(v, visited, nextSCC, this.invertedNeighbors);
                result.add(new LinkedHashSet<V>(nextSCC));
            }
        }
        return result;
    }

    /**
     * Starting from v we perform a depth first search.
     * @param v starting vertex
     * @param seen set of already visited vertics; will not be revisited
     * @param stack some stack; vertices are visited after recursion
     * @param currentNeighbors the current neighborhood where we walk around
     */
    private void dfs(
        final V v,
        final LinkedHashSet<V> seen,
        final LinkedList<V> stack,
        final LinkedHashMap<V, LinkedHashSet<V>> currentNeighbors)
    {
        seen.add(v);
        for (final V w : currentNeighbors.get(v)) {
            if (!seen.contains(w)) {
                this.dfs(w, seen, stack, currentNeighbors);
            }
        }
        stack.push(v);
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        this.export(eu, sb);
        return sb.toString();
    }

    protected void export(final Export_Util eu, final StringBuilder sb) {
        final Set<V> setOfVertices = this.getVertices();

        final LinkedHashMap<Integer, V> enumeration = new LinkedHashMap<>();
        final LinkedHashMap<V, Integer> inverseEnumeration = new LinkedHashMap<>();
        int index = 1;
        for (final V v : setOfVertices) {
            enumeration.put(index, v);
            inverseEnumeration.put(v, index);
            index++;
        }

        this.export(eu, sb, setOfVertices, index, inverseEnumeration, enumeration);
    }

    /**
     * Exports our graph.
     * @param eu some export helper
     * @param sb some string builder
     * @param setOfVertices set of vertices to be exported
     * @param index number of vertices
     * @param inverseEnumeration maps vertices to numbers
     * @param enumeration maps numbers to vertices
     */
    protected void export(
        final Export_Util eu,
        final StringBuilder sb,
        final Set<V> setOfVertices,
        final int index,
        final LinkedHashMap<V, Integer> inverseEnumeration,
        final LinkedHashMap<Integer, V> enumeration)
    {
        sb.append(eu.tttext("Nodes:"));
        sb.append(eu.linebreak());
        for (int i = 1; i < index; i++) {
            sb
                .append(eu.escape("("))
                .append(eu.export(i))
                .append(eu.escape(") "))
                .append(eu.export(enumeration.get(i)));
            sb.append(eu.linebreak());
        }
        sb.append(eu.linebreak());
        if (this.edges.isEmpty()) {
            sb.append(eu.tttext("No arcs!")).append(eu.linebreak());
            return;
        }
        sb.append(eu.tttext("Arcs:"));
        sb.append(eu.linebreak());
        for (final V v : setOfVertices) {
            final Set<V> ngbs = this.neighbors.get(v);
            if (ngbs.isEmpty()) {
                continue;
            }
            sb
                .append(eu.escape("("))
                .append(eu.export(inverseEnumeration.get(v)))
                .append(eu.escape(") "))
                .append(eu.rightarrow())
                .append(eu.escape(" "));
            boolean first = true;
            for (final V w : ngbs) {
                if (!first) {
                    sb.append(eu.escape(", "));
                }
                first = false;
                sb.append(eu.escape("(") + eu.export(inverseEnumeration.get(w)) + eu.escape(")"));
            }
            sb.append(eu.linebreak());
        }
    }

    @Override
    public String toString() {
        final PLAIN_Util pu = new PLAIN_Util();
        return this.export(pu);
    }
}
