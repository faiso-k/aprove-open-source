package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;

/**
 * This class represents a cycle in a graph, also called a strongly connected
 * component (SCC).
 * @author Peter Schneider-Kamp
 */
public class Cycle<N> extends LinkedHashSet<Node<N>> implements HTML_Able {

    /**
     * Serialize me!
     */
    private static final long serialVersionUID = 591676383911468809L;

    /**
     * flag to specify whether node numbers should be printed or not
     */
    protected boolean showNumbers = true;

    /**
     * Some nodes may be interesting. They are stored here.
     */
    private LinkedHashSet<Node<N>> interesting;

    /**
     * Creates a new cycle which is initially empty.
     */
    public Cycle() {
        super();
    }

    /**
     * Creates a cycle with a given set of nodes.
     * @param nodes The set of nodes for this cycle.
     */
    public Cycle(Set<Node<N>> nodes) {
        super(nodes);
    }

    /**
     * Add the given node and also mark it as interesting.
     * @param node the node to add
     * @return true iff the node was added
     */
    public boolean addInteresting(final Node<N> node) {
        if (this.interesting == null) {
            this.interesting = new LinkedHashSet<Node<N>>(1);
        }
        this.interesting.add(node);
        return super.add(node);
    }

    /**
     * @author Hermann Walth
     * @param originalGraph The graph from which this cycle was constructed
     * @return The set of edges that enter the cycle
     */
    public <E> Set<Edge<E, N>> getEntryEdges(SimpleGraph<N,E> originalGraph)
    {
        Set<Edge<E,N>> result = new LinkedHashSet<>();
        for(Node<N> target : this)
        {
            for (Node<N> origin : originalGraph.getIn(target))
            {
                if(!this.contains(origin))
                {
                    result.add(originalGraph.getEdge(origin, target));
                }
            }
        }
        return result;
    }

    /**
     * @author Hermann Walth
     * @param originalGraph The graph from which this cycle was constructed
     * @return The set of nodes that have edges entering the cycle, i.e., exactly
     * the end nodes of getEntryEdges()
     */
    public Set<Node<N>> getEntryNodes(SimpleGraph<N,?> originalGraph)
    {
        Set<Node<N>> result = new LinkedHashSet<>();
        for(Node<N> target : this)
        {
            for (Node<N> origin : originalGraph.getIn(target))
            {
                if (!this.contains(origin)) {
                    result.add(target);
                }
            }
        }
        return result;
    }

    /**
     * @author Hermann Walth
     * @param originalGraph The graph from which this cycle was constructed
     * @return The set of edges that leave the cycle
     */
    public <E> Set<Edge<E, N>> getExitEdges(SimpleGraph<N,E> originalGraph)
    {
        Set<Edge<E,N>> result = new LinkedHashSet<>();
        for(Node<N> origin : this)
        {
            for (Node<N> target : originalGraph.getOut(origin))
            {
                if(!this.contains(target)) {
                    result.add(originalGraph.getEdge(origin, target));
                }
            }
        }
        return result;
    }

    /**
     * @author Hermann Walth
     * @param originalGraph The graph from which this cycle was constructed
     * @return The set of nodes that have edges leaving the cycle, i.e., exactly
     * the start nodes of getExitEdges()
     */
    public Set<Node<N>> getExitNodes(SimpleGraph<N,?> originalGraph)
    {
        Set<Node<N>> result = new LinkedHashSet<>();
        for(Node<N> origin : this)
        {
            for (Node<N> target : originalGraph.getOut(origin))
            {
                if(!this.contains(target)) {
                    result.add(origin);
                }
            }
        }
        return result;
    }

    /**
     * @return the nodes marked interesting
     */
    public Collection<Node<N>> getInterestingNodes() {
        return this.interesting;
    }

    /**
     * Returns the user objects of all nodes of this cycle.
     * @return the user objects of all nodes of this cycle.
     */
    public Set<N> getNodeObjects() {
        Iterator<Node<N>> i = this.iterator();
        LinkedHashSet<N> objects = new LinkedHashSet<N>();
        while (i.hasNext()) {
            Node<N> node = i.next();
            objects.add(node.object);
        }
        return objects;
    }

    public boolean hasDirectEdgeTo(Cycle other, Graph graph) {
        Iterator<Node<N>> i = this.iterator();
        while (i.hasNext()) {
            Node<N> from = i.next();
            Iterator j = other.iterator();
            while (j.hasNext()) {
                Node to = (Node)j.next();
                if (graph.getOut(from).contains(to)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Determine if there should be an edge from this cycle to the given cycle
     * according to the given graph.
     * Bug: Maybe use reachable nodes and non-empty intersection instead of this.<br>
     * Bug: BUT: Do not compute transitive closure.
     */
    public boolean hasEdgeTo(Cycle other, Graph graph) {
/*        Set<Node> result = graph.determineReachableNodes(this);
        result.retainAll(other);
        return !result.isEmpty();*/
        Iterator<Node<N>> i = this.iterator();
        while (i.hasNext()) {
            Node<N> from = i.next();
            Iterator j = other.iterator();
            while (j.hasNext()) {
                Node to = (Node)j.next();
                if (graph.hasPath(from, to)) {
                    return true;
                }
            }
        }
        return false;
    }

    public void hideNodeNumbers() {
        this.showNumbers = false;
    }

    @Override
    public String toHTML() {
        StringBuffer temp = new StringBuffer();
        Export_Util eu = new HTML_Util();
        Iterator<Node<N>> i = this.iterator();
        while (i.hasNext()) {
            Node<N> node = i.next();
            temp.append("<B>");
            if (this.showNumbers) {
                temp.append(node.getNodeNumber()+": ");
            }
            temp.append(eu.export(node.object)+"</B>");
            if (i.hasNext()) {
                temp.append("<BR>");
            }
        }
        return temp.toString();
    }

    @Override
    public String toString() {
        Iterator<Node<N>> i = this.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append("{");
        while (i.hasNext()) {
            Node<N> node = i.next();
            sb.append(node.getNodeNumber());
            if (i.hasNext()) {
                sb.append(", ");
            }
        }
        sb.append("}");
        return sb.toString();
    }

}
