package aprove.verification.dpframework.BasicStructures;

/**
 * All possible (and interesting) rewrite strategies that we can analyze
 * for (probabilistic) term rewriting with the additional set Q, i.e., 
 * we already have a restriction to Q-rewriting but may allow parallel 
 * rewrite steps, etc.
 * 
 * @author jan-christoph
 * @version $Id$
 */
public enum QRewriteStrategy {

                              /** 
                               *  Full Q-rewriting, no restrictions. 
                               */
                              Q_FULL(false, "full"),
                              
                              /**
                               *  Parallel simultaneous rewriting. Only interesting in the probabilistic setting.
                               *  Multiple Q-redexes can be rewritten simultaneously such that the probabilities are
                               *  only used once (and not multiple times for all possible tuples of outcomes).
                               */
                              Q_PARALLEL_SIMULTANEOUS(true, "parallel-somultaneous");

    /** Can the rewrite strategy contract multiple redexes simultaneously? */
    private final boolean contractsMultipleRedexes;
    /** Representation of the strategy for proof descriptors, etc. */
    private final String representation;

    /**
     * @param contractsMultipleRedexes - can multiple redexes be rewritten
     *  in a single step?
     * @param representation - textual representation of the strategy for
     *  proof descriptors etc.
     */
    private QRewriteStrategy(boolean contractsMultipleRedexes, String representation) {
        this.contractsMultipleRedexes = contractsMultipleRedexes;
        this.representation = representation;
    }

    /**
     * @return whether this RewriteStrategy can contract multiple redexes
     *  in a single step
     */
    public boolean contractsMultipleRedexes() {
        return this.contractsMultipleRedexes;
    }

    /**
     * @return a String representation of this rewrite strategy
     */
    public String getRepresentation() {
        return this.representation;
    }
}
