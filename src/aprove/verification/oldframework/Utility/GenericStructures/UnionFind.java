package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;
import java.util.Map.Entry;

import immutables.*;

/**
 * Efficient Union-Find Algorithm.
 * <p>
 * The {@link #union} and {@link #find} operations have amortized constant running times (in this universe).
 * </p>
 * <p>
 * From: Efficiency of a Good But Not Linear Set Union Algorithm Journal of the ACM (JACM), Volume 22 Issue 2, April
 * 1975, 215 -- 225
 * </p>
 * <p>
 * Also see Wikipedia Article on the
 * <a href="http://en.wikipedia.org/wiki/Disjoint-set_data_structure">Disjoint-Set data structure</a>.
 * </p>
 * @param <T> The type of the elements of this union-find structure.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public final class UnionFind<T> {

    /**
     * Map from elements in this union-find structure to their corresponding nodes.
     */
    private final LinkedHashMap<T, Node> elements = new LinkedHashMap<T, Node>();

    /**
     * @param t Some element.
     * @return The representative element for the specified one in this union-find structure.
     */
    public T find(T t) {
        return this.lookup(this.getNode((t))).element;
    }

    /**
     * @param t Some element.
     * @return The equivalence class containing the specified element.
     */
    public ImmutableSet<T> getPartition(T t) {
        Node rep = this.lookup(this.getNode(t));
        Set<T> res = new LinkedHashSet<T>();
        for (Node e : this.elements.values()) {
            if (rep == this.lookup(e)) {
                res.add(e.element);
            }
        }
        return ImmutableCreator.create(res);
    }

    /**
     * Compute all equivalence classes, without ignored elements.
     * @return An immutable set of immutable sets of elements representing the partition of all elements in this
     *         union-find structure according to their equivalence classes.
     */
    public ImmutableSet<ImmutableSet<T>> getPartitions() {
        Map<Node, Set<T>> partitions = new LinkedHashMap<Node, Set<T>>();
        for (Entry<T, Node> e : this.elements.entrySet()) {
            Node partitionNode = this.lookup(e.getValue());
            Set<T> members = partitions.get(partitionNode);
            if (members == null) {
                members = new LinkedHashSet<>();
                partitions.put(partitionNode, members);
            }
            members.add(e.getKey());
        }
        Set<ImmutableSet<T>> almostImmutablePartitions =
            new LinkedHashSet<ImmutableSet<T>>();
        for (Set<T> e : partitions.values()) {
            almostImmutablePartitions.add(ImmutableCreator.create(e));
        }
        return ImmutableCreator.create(almostImmutablePartitions);
    }

    /**
     * Treat all further occurrences of {@code t} as distinct from former occurrences.
     * <p>
     * This is useful for locally bound variables for example.
     * </p>
     * @param t Some element.
     */
    public void ignore(T t) {
        this.elements.remove(t);
    }

    /**
     * States that all elements in {@code ts} belong to the same equivalence class.
     * @param ts An iteration of elements.
     */
    public void union(Iterable<T> ts) {
        Iterator<T> it = ts.iterator();
        if (!it.hasNext()) {
            return;
        }
        T first = it.next();
        while (it.hasNext()) {
            T next = it.next();
            this.union(first, next);
        }
    }

    /**
     * States that {@code t1} and {@code t2} belong to the same equivalence class.
     * @param t1 Some element.
     * @param t2 Another element.
     */
    public void union(T t1, T t2) {
        Node e1 = this.lookup(this.getNode((t1)));
        Node e2 = this.lookup(this.getNode((t2)));
        if (e1 == e2) {
            return;
        }
        if (e1.rank > e2.rank) {
            e2.parent = e1;
        } else if (e2.rank > e1.rank) {
            e1.parent = e2;
        } else {
            e1.parent = e2;
            e1.rank++;
        }
    }

    /**
     * @param t Some element.
     * @return The corresponding node for the specified element. If the element has not yet been contained in this
     *         union-find structure, it is added and the newly created node for this element is returned.
     */
    private Node getNode(T t) {
        Node n = this.elements.get(t);
        if (n == null) {
            n = new Node(t);
            this.elements.put(t, n);
        }
        return n;
    }

    /**
     * Retrieves the representative node for the specified one and performs path compression during retrieval.
     * @param n Some node.
     * @return The representative node of the equivalence class to which the specified node belongs.
     */
    private Node lookup(Node n) {
        if (n.parent == n) {
            return n;
        }
        n.parent = this.lookup(n.parent); // shorten path to root
        return n.parent;
    }

    /**
     * A node of the union-find structure.
     * @author unknown, cryingshadow
     * @version $Id$
     */
    private class Node {

        /**
         * The element represented by this node.
         */
        private final T element;

        /**
         * The parent of this node. The representative node of an equivalence class points to itself.
         */
        private Node parent;

        /**
         * The rank of this node.
         */
        private int rank;

        /**
         * @param elem The element represented by this node.
         */
        public Node(T elem) {
            this.parent = this;
            this.rank = 0;
            this.element = elem;
        }

    }

}
