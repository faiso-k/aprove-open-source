/**
 *
 */
package aprove.verification.oldframework.IRSwT.Digraph;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Representation of an edge-labeled digraph.
 * @author Matthias Hoelzel
 * @param <V> type of nodes
 * @param <L> type of labels
 */
public class LabeledDigraph<V, L> extends Digraph<V> {
    /**
     * Maps every edge to a set of labels.
     */
    protected LinkedHashMap<Pair<V, V>, LinkedHashSet<L>> labels;

    /**
     * Create a new labeled directed graph.
     * @param initialVertices initial vertices
     * @param initialEdges edges to start with. edges from or to nodes which
     * are not in the set of initial vertices are ignored!
     */
    public LabeledDigraph(final Collection<V> initialVertices, final Collection<Pair<V, V>> initialEdges) {
        super(initialVertices, initialEdges);
        this.labels = new LinkedHashMap<>();
    }

    /**
     * Create an empty labelled digraph.
     */
    public LabeledDigraph() {
        super();
        this.labels = new LinkedHashMap<>();
    }

    /**
     * Adds a label to a given edge.
     * Please that this edge must exist.
     * @param edge pair of nodes
     * @param l some label
     */
    private void addLabel(final Pair<V, V> edge, final L l) {
        if (this.isFrozen()) {
            throw new UnsupportedOperationException("Cannot modify frozen data structur!");
        }
        if (!this.isConnected(edge.x, edge.y)) {
            throw new UnsupportedOperationException("Cannot add label to non-existent edge!");
        } else {
            this.checkAndGetLabels(edge).add(l);
        }
    }

    /**
     * Adds a label to a given edge.
     * Please that this edge must exist.
     *
     * @param u first node
     * @param v second node
     * @param l some label
     */
    public void addLabel(final V u, final V v, final L l) {
        this.addLabel(new Pair<V, V>(u, v), l);
    }

    /**
     * Remove a label of a given edge.
     * Please that this edge must exist.
     *
     * @param edge pair of nodes
     * @param l some label
     */
    private void removeLabel(final Pair<V, V> edge, final L l) {
        if (this.isFrozen()) {
            throw new UnsupportedOperationException("Cannot modify frozen data structur!");
        }
        if (!this.isConnected(edge.x, edge.y)) {
            throw new UnsupportedOperationException("Cannot modify label set of non-existent edge!");
        } else {
            this.checkAndGetLabels(edge).remove(l);
        }
    }

    /**
     * Remove a label of a given edge.
     * Please that this edge must exist.
     * @param u first node
     * @param v second node
     * @param l some label
     */
    public void removeLabel(final V u, final V v, final L l) {
        this.removeLabel(new Pair<V, V>(u, v), l);
    }

    /**
     * Connects u and v and directly adds a label.
     * If the edge already exists, then only the label will be added.
     * @param u first node
     * @param v second node
     * @param l some label
     */
    public void connect(final V u, final V v, final L l) {
        super.connect(u, v);
        this.checkAndGetLabels(new Pair<V, V>(u, v)).add(l);
    }

    /**
     * Removes the edge again. Additionally it remove the label set.
     * If frozen, then we throw an error.
     * @param u vertex where you start
     * @param v vertex where you end
     */
    @Override
    public void disconnect(final V u, final V v) {
        super.disconnect(u, v);
        this.labels.remove(new Pair<V, V>(u, v));
    }

    /**
     * Returns a of label, iff u and v are connected. null, otherwise.
     * @param u first node
     * @param v second node
     * @return set of labels
     */
    public ImmutableLinkedHashSet<L> getLabels(final V u, final V v) {
        return this.getLabels(new Pair<V, V>(u, v));
    }

    /**
     * Returns a of label, iff u and v are connected. null, otherwise.
     * @param edge current edge
     * @return set of labels
     */
    private ImmutableLinkedHashSet<L> getLabels(final Pair<V, V> edge) {
        if (this.isConnected(edge.x, edge.y)) {
            return ImmutableCreator.create(this.checkAndGetLabels(edge));
        } else {
            return null;
        }
    }

    /**
     * Returns set currently used set of labels. Creates
     * one, if it does not already exist.
     * @param edge current edge
     * @return set of labels
     */
    private LinkedHashSet<L> checkAndGetLabels(final Pair<V, V> edge) {
        if (!this.labels.containsKey(edge) || this.labels.get(edge) == null) {
            this.labels.put(edge, new LinkedHashSet<L>());
        }
        return this.labels.get(edge);
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        this.export(eu, sb);
        return sb.toString();
    }

    @Override
    public void export(final Export_Util eu, final StringBuilder sb) {
        super.export(eu, sb);
        sb.append(eu.linebreak());
        sb.append(eu.tttext("Labels:"));
        sb.append(eu.linebreak());
        for (final Entry<Pair<V, V>, LinkedHashSet<L>> e : this.labels.entrySet()) {
            sb
                .append(eu.export(e.getKey().x))
                .append(eu.rightarrow())
                .append(eu.export(e.getKey().y))
                .append(eu.tttext(": "));
            for (final L label : e.getValue()) {
                sb.append(eu.export(label));
                sb.append(eu.tttext(" "));
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
