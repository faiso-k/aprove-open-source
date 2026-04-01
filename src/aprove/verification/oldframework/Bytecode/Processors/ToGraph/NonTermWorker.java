package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Common superclass of workers that try to prove nontermination.
 *
 * @author Marc Brockschmidt
 */
public abstract class NonTermWorker extends MethodGraphWorker {
    /**
     * max allowed number of NonTermWorkers
     */
    public static final int MAX = 10;
    /**
     * counts the number of occassisions on which we started a NonTermWorker
     */
    public static int numberOfStartedWorkers = 0;
    /**
     * The node for which a witness is searched.
     */
    private final Node interestingNode;

    /**
     * @param graph some method graph
     * @param iNode some node for which a witness (a state that is an instance
     *  of the method's start state) should be generated.
     */
    public NonTermWorker(final MethodGraph graph, final Node iNode) {
        super(graph);
        this.interestingNode = iNode;
    }

    /**
     * @return the node which indicates that we should search for nontermination.
     */
    protected Node getInterestingNode() {
        return this.interestingNode;
    }

    /**
     * @return a filter that does not accept invalid method skip edges
     * @param methodGraph the method graph of the edges the filter sees
     */
    public static EdgeFilter getEdgeFilter(final MethodGraph methodGraph) {
        return new EdgeFilter() {
            private final MethodGraph mg = methodGraph;

            @Override
            public boolean selectEdge(final Node from, final Node to, final EdgeInformation e) {
                if (e instanceof MethodSkipEdge) {
                    final MethodSkipEdge mse = (MethodSkipEdge) e;
                    if (mse.getNode() == null) {
                        return false;
                    }
                }
                return true;
            }
        };
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.interestingNode == null) ? 0 : this.interestingNode.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final NonTermWorker other = (NonTermWorker) obj;
        if (this.interestingNode == null) {
            if (other.interestingNode != null) {
                return false;
            }
        } else if (!this.interestingNode.equals(other.interestingNode)) {
            return false;
        }
        return true;
    }
}
