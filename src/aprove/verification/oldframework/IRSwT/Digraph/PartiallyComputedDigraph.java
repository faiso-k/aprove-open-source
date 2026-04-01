package aprove.verification.oldframework.IRSwT.Digraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Represents a fully or partially computed digraph.
 * A pair (u,v) of this graph has either been evaluated or not.
 * If (u,v) has been evaluated, then we know whether (u,v) is an arc
 * of this digraph or not. Otherwise we can only use rough estimations.
 *
 * The status of edges is changed to evaluated as soon as you call either connect()
 * or disconnect(). Here disconnect() explicitly indicates that some arc does not exist.
 * Additionally, graphs created from existing data structures
 * are assumed to be fully evaluated.
 *
 * @author Matthias Hoelzel
 * @param <V> type of vertices; should be hashable.
 *
 */
public class PartiallyComputedDigraph<V> extends Digraph<V> {

    /**
     * Lists the evaluated pairs.
     */
    private final LinkedHashSet<Pair<V, V>> evaluatedPairs;

    /**
     * Create an empty digraph.
     */
    public PartiallyComputedDigraph() {
        this.evaluatedPairs = new LinkedHashSet<>();
    }

    /**
     * Creates digraph with given vertices and edges.
     * @param initialVertices initial vertices
     * @param initialEdges initial edges
     */
    public PartiallyComputedDigraph(final Collection<V> initialVertices, final Collection<Pair<V, V>> initialEdges) {
        super(initialVertices, initialEdges);
        this.evaluatedPairs = new LinkedHashSet<>();
        for (final V u : initialVertices) {
            for (final V v : initialVertices) {
                this.evaluatedPairs.add(new Pair<>(u, v));
            }
        }
    }

    /**
     * Creates a copy of this. Useful for creating a copy of a frozen digraph,
     * that can be modified again.
     * @param dig some digraph
     */
    public PartiallyComputedDigraph(final PartiallyComputedDigraph<V> dig) {
        super(dig);
        this.evaluatedPairs = new LinkedHashSet<>(dig.evaluatedPairs);
    }

    /**
     * Creates digraph with given vertices. This graph has not be evaluated.
     * @param initialVertices initial vertices
     */
    public PartiallyComputedDigraph(final Collection<V> initialVertices) {
        super(initialVertices, new LinkedHashSet<Pair<V, V>>());
        this.evaluatedPairs = new LinkedHashSet<>();
    }

    @Override
    public void removeVertex(final V v) {
        for (final V u : this.getVertices()) {
            this.evaluatedPairs.remove(new Pair<>(u, v));
            this.evaluatedPairs.remove(new Pair<>(v, u));
        }
        super.removeVertex(v);

    }

    @Override
    public void connect(final V from, final V to) {
        super.connect(from, to);
        this.evaluatedPairs.add(new Pair<V, V>(from, to));
    }

    @Override
    public void disconnect(final V from, final V to) {
        super.disconnect(from, to);
        this.evaluatedPairs.add(new Pair<V, V>(from, to));
    }

    @Override
    public boolean isFullyEvaluated() {
        final Set<V> vertices = this.getVertices();
        for (final V v : vertices) {
            for (final V u : vertices) {
                if (!this.evaluatedPairs.contains(new Pair<>(u, v))) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Returns true, iff we have already checked whether (v,w) should
     * be an arc.
     * @param v node where you start
     * @param w node where you (might) end
     * @return boolean
     */
    public boolean isEvaluated(final V v, final V w) {
        return this.evaluatedPairs.contains(new Pair<>(v, w));
    }

    /**
     * Adds every possible (not-evaluated) edge,
     * but does not change the evaluation status.
     */
    public void overestimate() {
        final Set<V> vertices = this.getVertices();
        for (final V v : vertices) {
            for (final V w : vertices) {
                if (!this.evaluatedPairs.contains(new Pair<V, V>(v, w))) {
                    super.connect(v, w);
                }
            }
        }
    }

    /**
     * Removes every possible (not-evaluated) edge,
     * but does not change the evaluation status.
     */
    public void underestimate() {
        final Set<V> vertices = this.getVertices();
        for (final V v : vertices) {
            for (final V w : vertices) {
                if (!this.evaluatedPairs.contains(new Pair<V, V>(v, w))) {
                    super.disconnect(v, w);
                }
            }
        }
    }

    @Override
    public PartiallyComputedDigraph<V> getInducedSubgraph(final Set<V> newVertices) {
        final PartiallyComputedDigraph<V> result = new PartiallyComputedDigraph<>(newVertices);
        for (final V v : newVertices) {
            for (final V w : newVertices) {
                if (this.isConnected(v, w)) {
                    result.connect(v, w);
                } else {
                    result.disconnect(v, w);
                }
                if (this.evaluatedPairs.contains(new Pair<V, V>(v, w))) {
                    result.evaluatedPairs.add(new Pair<V, V>(v, w));
                }
            }
        }
        return result;
    }

    @Override
    protected void export(
        final Export_Util eu,
        final StringBuilder sb,
        final Set<V> setOfVertices,
        final int index,
        final LinkedHashMap<V, Integer> inverseEnumeration,
        final LinkedHashMap<Integer, V> enumeration)
    {
        super.export(eu, sb, setOfVertices, index, inverseEnumeration, enumeration);

        if (this.isFullyEvaluated()) {
            sb.append(eu.linebreak());
            sb.append(eu.tttext("This digraph is fully evaluated!"));
            return;
        }
        sb.append(eu.linebreak());
        sb.append(eu.tttext("Not evaluated pairs:"));
        sb.append(eu.linebreak());
        boolean first = true;
        for (final V v : setOfVertices) {
            for (final V w : setOfVertices) {
                if (!this.evaluatedPairs.contains(new Pair<>(v, w))) {
                    if (!first) {
                        sb.append(eu.escape(", "));
                    }
                    first = false;
                    sb
                        .append(eu.escape("("))
                        .append(eu.export(inverseEnumeration.get(v)))
                        .append(eu.escape(", "))
                        .append(eu.export(inverseEnumeration.get(w)))
                        .append(eu.escape(")"));
                }
            }
        }
    }

    /**
     * Returns a mapped graph.
     * @param newNodes the new nodes
     * @param map some mapping, should be bijective
     * @return graph
     */
    public PartiallyComputedDigraph<V> translateNodes(final Set<V> newNodes, final LinkedHashMap<V, V> map) {
        final PartiallyComputedDigraph copy = new PartiallyComputedDigraph(newNodes);
        for (final V v : this.getVertices()) {
            for (final V w : this.getVertices()) {
                final V vMapped = map.containsKey(v) ? map.get(v) : v;
                final V wMapped = map.containsKey(w) ? map.get(w) : w;

                if (this.isConnected(v, w)) {
                    copy.connect(v, w);
                }

                if (this.evaluatedPairs.contains(new Pair<V, V>(v, w))) {
                    copy.evaluatedPairs.add(new Pair<V, V>(vMapped, wMapped));
                }
            }
        }

        return copy;
    }
}
