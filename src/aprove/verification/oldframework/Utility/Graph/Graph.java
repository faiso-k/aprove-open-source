package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

/**
 * A Graph is like a simple graph but it additionally stores
 * links from nodes objects to corresponding nodes. Hence, in this
 * kind of graph one is not allowed to change node objects.
 * If you want to be able to change node objects, use the
 * ChangeableGraph.
 * @author thiemann
 * @version $Id$
 */
public class Graph<N,E> extends SimpleGraph<N,E> {

    private static final long serialVersionUID = 1705522184496046873L;

    /**
     * A mapping from user objects to a set of nodes.
     */
    protected LinkedHashMap<N,Set<Node<N>>> nodeObjectMap;

    public Graph(Set<Node<N>> nodes, SimpleGraph<N,E> subgraph) {
        super(nodes, subgraph);
        this.checkNodeObjectMap();
    }

    public Graph() {
        super();
        this.checkNodeObjectMap();
    }

    public Graph(Set<Node<N>> nodes) {
        super(nodes);
        this.checkNodeObjectMap();
    }

    public Graph(Set<Node<N>> nodes, Set<Edge<E,N>> edges) {
        super(nodes, edges);
        this.checkNodeObjectMap();
    }

    private Graph(Graph<N, E> other) {
        super(other);
        this.nodeObjectMap = new LinkedHashMap<N, Set<Node<N>>>(other.nodeObjectMap);
        for (Map.Entry<N, Set<Node<N>>> entry : this.nodeObjectMap.entrySet()) {
            entry.setValue(new LinkedHashSet<Node<N>>(entry.getValue()));
        }
    }

    private void checkNodeObjectMap() {
        if (this.nodeObjectMap == null) {
            this.nodeObjectMap = new LinkedHashMap<N, Set<Node<N>>>();
        }
    }

    @Override
    public Graph<N, E> getSubGraph(Set<Node<N>> nodes) {
        return new Graph<N, E>(nodes, this);
    }

    @Override
    public Graph<N, E> getCopy() {
        return new Graph<N, E>(this);
    }

    @Override
    public boolean addNode(Node<N> node) {
        this.checkNodeObjectMap();
        boolean res = super.addNode(node);
        if (res) {
            N obj = node.object;
            if (obj != null) {
                Set<Node<N>> nSet = this.nodeObjectMap.get(obj);
                if (nSet == null) {
                    nSet = new LinkedHashSet<Node<N>>();
                    this.nodeObjectMap.put(obj, nSet);
                }
                nSet.add(node);
            }
        }
        return res;
    }

    @Override
    public void clearGraph() {
        super.clearGraph();
        this.nodeObjectMap.clear();
    }

    @Override
    void removeNode(Node<N> node, Map<Node<N>, E> outMap) {
        super.removeNode(node, outMap);
        Set<Node<N>> nSet = this.nodeObjectMap.get(node.object);
        if (nSet != null) {
            nSet.remove(node);
            if (nSet.isEmpty()) {
                this.nodeObjectMap.remove(node.object);
            }
        }
    }

    @Override
    public void setNodeObject(Node<N> node, N label) {
        N oldLabel = node.object;
        // if the labels are identical there is nothing todo
        if (oldLabel != label && (oldLabel == null || !oldLabel.equals(label))) {
            // remove old label
            if (oldLabel != null) {
                Set<Node<N>> nodes = this.nodeObjectMap.get(oldLabel);
                if (nodes == null || !nodes.remove(node)) {
                    throw new RuntimeException("Nodelabel map invalid!\n");
                } else {
                    if (nodes.isEmpty()) {
                        this.nodeObjectMap.remove(oldLabel);
                    }
                }
            }

            // and add new label
            if (label != null) {
                Set<Node<N>> nodes = this.nodeObjectMap.get(label);
                if (nodes == null) {
                    nodes = new HashSet<Node<N>>();
                    this.nodeObjectMap.put(label, nodes);
                }
                nodes.add(node);
            }
        }

        super.setNodeObject(node, label);
    }

    /**
     * Return the node that is associated with the given object.
     * <p>
     * Note: If the same object is associated to more than one node
     *       an arbitrary node is returned
     **/
    public Node<N> getNodeFromObject(N object) {

        Set<Node<N>> nodes = this.nodeObjectMap.get(object);
        if (nodes != null && !nodes.isEmpty()) {
            return nodes.iterator().next();
        }
        return null;
    }

    /**
     * Return all nodes that are associated with the given object.
     **/
    public Set<Node<N>> getAllNodesFromObject(N object) {

        return this.nodeObjectMap.get(object);

    }



    /**
     * Returns a set containing the objects of some nodes of this graph.
     * @return A set of the objects of some nodes of this graph.
     * (the set is fresh, so it could be modified, without changing the graph)
     */
    public Set<N> getObjectsFromNodes(Collection<Node<N>> nodes){
        Set<N> res = new LinkedHashSet<N>();
        for (Node<N> node : nodes){
            res.add(node.getObject());
        }
        return res;
    }

    /**
     * Returns a set containing the objects of all nodes of this graph.
     * @return A set of the objects of all nodes of this graph.
     */
    public Set<N> getNodeObjects() {

        return this.nodeObjectMap.keySet();

    }


    /**
     * Gets all nodes, which are associated with a specified set of
     * objects
     *
     * @param objects a <code>Collection</code> of object to which the
     * associated nodes should be retrieved
     * @return all nodes associated with the specified objects
     */
    public Set<Node<N>> getNodesFromObjects(Collection<N> objects) {

        Set<Node<N>> result = new LinkedHashSet<Node<N>>();
        for (N object : objects) {
            Set<Node<N>> nodes = this.nodeObjectMap.get(object);
            if (nodes != null) {
                result.addAll(nodes);
            }
        }
        return result;
    }


}