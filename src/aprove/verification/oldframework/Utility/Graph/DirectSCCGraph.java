package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

public class DirectSCCGraph<N, E> extends SCCGraph<N, E> {

    /**
     * Create an empty directSCC graph for a given graph.
     */
    public DirectSCCGraph() {
        super();
    }

    /**
     * Creates a directSCC graph with the SCCs of the given graph.
     */
    public DirectSCCGraph(Graph<N, E> graph) {
        this(graph.getSCCs(), graph);
    }

    /**
     * Creates a directSCC graph with the SCCs of the given
     * graph.
     */
    public DirectSCCGraph(Graph<N,E> graph, boolean onlyReal) {
        this(graph.getSCCs(onlyReal), graph);
    }

    /**
     * Creates a directSCC graph consisting of the given cycles
     * with connections between them according to a given graph.
     */
    public DirectSCCGraph(Set<Cycle<N>> sccs, Graph<N,E> graph) {
        this();
        this.origin = graph;
        for (Cycle<N> scc : sccs) {
            this.addNode(new Node<Cycle<N>>(scc));
        }
        for (Node<Cycle<N>> from : this.getNodes()) {
            Cycle<N> fromCycle = from.object;
            for (Node<Cycle<N>> to : this.getNodes()) {
                Cycle<N> toCycle = to.object;
                if (!fromCycle.equals(toCycle) && fromCycle.hasDirectEdgeTo(toCycle, graph)) {
                    this.addEdge(from, to);
                }
            }
        }

    }
}
