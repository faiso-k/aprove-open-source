package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

/**
 * Simple DAG structure a.k.a. tree, adding nodes only via add edge. Removal of non-leaf nodes is forbidden
 * @author marinag
 * @param <N> Node class
 * @param <E> Edge class
 */
public class SimpleTree<N, E> extends SimpleGraph<N, E> {

    /**
     *
     */
    private static final long serialVersionUID = -5155869830365424145L;

    /**
     * Tree root node
     */
    final private Node<N> root;

    /**
     * @param root tree root node
     */
    public SimpleTree(final Node<N> root) {
        super();
        super.addNode(root);
        this.root = root;
    }

    /**
     * @param node tree node
     * @return list of node's ancestors from the tree root including the node itself. Returns null if node doesn't exist in the tree.
     */
    public List<Node<N>> getAncestorsInclusive(final Node<N> node) {
        return this.getPath(this.root, node);
    }

    /**
     * @param node tree node
     * @return list of node's ancestors from the tree root not including the node itself. Returns null if node doesn't exist in the tree.
     */
    public List<Node<N>> getAncestors(final Node<N> node) {
        final Node<N> father = this.getFather(node);

        if (father == null) {
            return new ArrayList<>();
        }
        return this.getAncestorsInclusive(father);
    }

    /**
     * @return tree's root node
     */
    public Node<N> getRoot() {
        return this.root;
    }


    /**
     * @param node tree node
     * @return node's father node, if node is a root node or doesn't exist in the tree - returns null.
     */
    public Node<N> getFather(final Node<N> node) {
        if (this.isRoot(node)) {
            return null;
        }

        final Set<Node<N>> parents = this.getIn(node);
        assert parents.size() == 1;
        return parents.iterator().next();
    }

    /**
     * @param node - tree node
     * @return the single edge that ends at the given node
     */
    public Edge<E, N> getInEdge(final Node<N> node) {
        if (this.isRoot(node)) {
            return null;
        }

        final Set<Edge<E, N>> inEdges = this.getInEdges(node);
        assert inEdges.size() == 1;

        return inEdges.iterator().next();
    }

    /**
     * @param node tree node
     * @return true if node is the root, false otherwise
     */
    public boolean isRoot(final Node<N> node) {
        return this.getRoot().equals(node);
    }

    /**
     * @param node tree node
     * @return true if appears in the tree and has no out edges, false otherwise
     */
    public boolean isLeaf(final Node<N> node) {
        return this.nodes.contains(node) && this.getOutEdges(node).isEmpty();
    }

    /**
     * @param a first tree node
     * @param b second tree node
     * @return true if the first node is an ancestor of the second node in the tree
     */
    public boolean isAncestorOf(final Node<N> a, final Node<N> b) {
        final List<Node<N>> ancestors = this.getAncestors(b);
        return ancestors != null && ancestors.contains(a);
    }

    /**
     * @return set of nodes that have no out edges (aka leaves)
     */
    public Set<Node<N>> getLeaves() {
        final Set<Node<N>> leaves = new HashSet<>();

        for (final Node<N> node : this.getNodes()) {
            if (this.isLeaf(node)) {
                leaves.add(node);
            }
        }

        return leaves;
    }

    /**
     * @param node tree node
     * @return set of nodes that can be reached from the given node (aka descendants)
     */
    public Set<Node<N>> getDescendants(final Node<N> node) {
        return this.determineReachableNodes(Arrays.asList(node));
        //
        //        final HashSet<Node<N>> descendants = new HashSet<>();
        //        final Set<Node<N>> children = this.getOut(node);
        //        descendants.addAll(children);
        //
        //        for (final Node<N> c : children) {
        //            descendants.addAll(this.getDescendants(c));
        //        }
        //        return descendants;
    }

    /**
     * @param a first tree node
     * @param b second tree node
     * @return nearest common ancestor of both the first and the second node. If one or both of the nodes aren't present in the tree, returns null.
     */
    public Node<N> nearestCommonAncestor(final Node<N> a, final Node<N> b) {
        if (!this.contains(a) || !this.contains(b)) {
            return null;
        }

        final List<Node<N>> anc = new ArrayList<Node<N>>(this.getAncestorsInclusive(a));
        Collections.reverse(anc);
        for (final Node<N> w : anc) {
            if (b.equals(w) || this.getAncestors(b).contains(w)) {
                return w;
            }
        }
        return this.root;
    }

    /**
     * @param node tree node
     * @return list of nodes from the root to the given node
     */
    public List<Node<N>> getPathFromRoot(final Node<N> node) {
        return this.getPath(this.root, node);
    }

    /**
     * @param node tree node
     * @return list of edges from the root to the given node
     */
    public List<Edge<E, N>> getEdgesPathFromRoot(final Node<N> node) {

        final List<Edge<E, N>> edges = new ArrayList<>();

        for (final Node<N> n : this.getPath(this.root, node)) {
            if (this.isRoot(n)) {
                continue;
            }
            edges.add(this.getInEdge(n));
        }

        return edges;
    }

    //    /**
    //     * Leaf validations
    //     * @param node tree node
    //     * @throws UnsupportedException in case node is not a leaf.
    //     */
    //    private void validateLeaf(final Node<N> node) throws UnsupportedException {
    //        if (!this.isLeaf(node)) {
    //            throw new UnsupportedException("Leaf excpected");
    //        }
    //    }


    @Override
    public boolean addEdge(final Node<N> start, final Node<N> end, final E label) {
        assert !this.contains(end) && this.contains(start); // || !this.hasPath(end, start) : "Cycle";
        super.addNode(end);
        return super.addEdge(start, end, label);
    }


    @Override
    public boolean addNode(final Node<N> node) {
        return false;
        //        if (!this.contains(node)) {
        //            throw new UnsupportedOperationException();
        //        }
        //        return super.addNode(node);
    }

    @Override
    public boolean removeNode(final Node<N> node) {
        if (!this.isLeaf(node)) {
            return false;
        }

        return super.removeNode(node);
    }

    @Override
    public void removeEdge(final Edge<E, N> edge) {
        if (!this.isLeaf(edge.getEndNode())) {
            return ;
        }

        super.removeEdge(edge);
    }

    @Override
    public void removeEdge(final Node<N> start, final Node<N> end) {
        if (!this.isLeaf(end)) {
            return;
        }

        super.removeEdge(start, end);
    }

    @Override
    public E removeEdgeAndReturnLabel(final Node<N> start, final Node<N> end) {
        if (!this.isLeaf(end)) {
            return null;
        }

        return super.removeEdgeAndReturnLabel(start, end);
    }

    /**
     * Merges the node and all its descendant into one node
     * @param node tree node
     * @param labelMerger
     * @param edgeMerger
     * @return the node to which the given node and its descendants were merged into.
     */
    public Node<N> merge(
        final Node<N> node,
        final BinaryOperation<N> labelMerger,
        final BinaryOperation<E> edgeMerger)
        {

        final Set<Node<N>> replaceUs = this.getDescendants(node);
        replaceUs.add(node);
        return super.merge(replaceUs, labelMerger, edgeMerger);

        }

    @Override
    public Node<N> merge(
        final Set<Node<N>> replaceUs,
        final BinaryOperation<N> labelMerger,
        final BinaryOperation<E> edgeMerger)
        {

        return null;

        }
}
