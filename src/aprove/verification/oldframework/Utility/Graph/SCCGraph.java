package aprove.verification.oldframework.Utility.Graph;

import java.util.*;
import java.util.logging.*;

/**
 * This class represents a directed graph acyclic graph of SCCs.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class SCCGraph<N,E> extends Graph<Cycle<N>,E> {

    public static Logger log = Logger.getLogger("aprove.verification.oldframework.Utility.Graph.SCCGraph");

    protected Graph<N,E> origin;

    /**
     * Create an empty SCC graph for a given graph.
     */
    public SCCGraph() {

        super();
        this.origin = null;

    }

    /**
     * Creates a SCC graph with the SCCs of the given
     * graph.
     */
    public SCCGraph(Graph<N,E> graph) {
        this(graph.getSCCs(), graph, false);
    }

    /**
     * Creates a SCC graph with the SCCs of the given
     * graph.
     */
    public SCCGraph(Graph<N,E> graph, boolean onlyReal) {
        this(graph, onlyReal, false);
    }

    /**
     * Creates a SCC graph with the SCCs of the given
     * graph.
     */
    public SCCGraph(Graph<N,E> graph, boolean onlyReal, boolean directEdges) {
        this(graph.getSCCs(onlyReal), graph, directEdges);
    }

    /**
     * Creates a SCC graph consisting of the given cycles with connections between them according to a given graph.
     */
    public SCCGraph(final Set<Cycle<N>> sccs, final Graph<N, E> graph) {
        this(sccs, graph, false);
    }

    /**
     * Creates a SCC graph consisting of the given cycles
     * with connections between them according to a given graph.
     */
    public SCCGraph(Set<Cycle<N>> sccs, Graph<N,E> graph, boolean directEdges) {

        this();
        this.origin = graph;
        for (Cycle<N> scc : sccs) {
            this.addNode(new Node<Cycle<N>>(scc));
        }
        for (Node<Cycle<N>> from : this.getNodes()) {
            Cycle<N> fromCycle = from.object;
            for (Node<Cycle<N>> to : this.getNodes()) {
                Cycle<N> toCycle = to.object;
                if (!fromCycle.equals(toCycle) && ((directEdges && fromCycle.hasDirectEdgeTo(toCycle, graph)) || (!directEdges && fromCycle.hasEdgeTo(toCycle, graph)))) {
                    this.addEdge(from, to);
                }
            }
        }

    }

    /**
     * Determines a permutation of all SCCs in this condensed graph
     * in a way that the first SCC does not have any outgoing paths to other
     * SCCs, the second one has only outgoing paths to the first, and so on
     * @return A list of SCCs.
     */
    public List<Cycle<N>> getRankedSCCs() {

        List<Cycle<N>> result = new Vector<Cycle<N>>();
        for (Set<Node<Cycle<N>>> temp : this.getRanks()) {
            for (Node<Cycle<N>> node : temp) {
                result.add(node.object);
            }
        }
        return result;

    }

    /**
     *
     */
    public Set<Node<Cycle<N>>> getSCCsReachableFrom(Collection<N> objects) {
        List<Node<Cycle<N>>> start = new ArrayList<Node<Cycle<N>>>();
        for (N object : objects){
            start.add(this.getSccNodeFromObject(object));
        }
        return this.determineReachableNodes(start);
    }

    /**
     * Return the SCC that contains the given object.
     **/
    public Cycle<N> getSccFromObject(N object) {
        Node<N> object_node = this.origin.getNodeFromObject(object);
        if (object_node == null) {
            return null;
        }
        for (Node<Cycle<N>> node : this.getNodes()) {
            Cycle<N> scc = node.object;
            if (scc.contains(object_node)) {
                return scc;
            }
        }
        return null;
    }

    /**
     * Return the SCCNode that contains the given object.
     **/
    public Node<Cycle<N>> getSccNodeFromObject(N object) {
        Node<N> object_node = this.origin.getNodeFromObject(object);
        if (object_node == null) {
            return null;
        }
        for (Node<Cycle<N>> node : this.getNodes()) {
            Cycle<N> scc = node.object;
            if (scc.contains(object_node)) {
                return node;
            }
        }
        return null;
    }

}
