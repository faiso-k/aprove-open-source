package aprove.verification.dpframework.BasicStructures;

/**
 * Enum to represent rewrite strategies that are not further parameterized,
 * such as innermost, parallel-innermost, outermost, ... rewriting. Here
 * parameterized rewrite strategies include, e.g., context-sensitive rewrite
 * strategies, which depend on a given signature. RewriteStrategy objects can
 * be queried whether they allow for contraction of multiple redexes in a
 * single rewrite step (i.e., whether they are "multistep strategies").
 *
 * @author fuhs
 *
 */
public enum RewriteStrategy {
    /** Full rewriting, no restrictions. */
    FULL(false, "full"),
    /**
     *  Innermost rewriting. Only innermost redexes can be rewritten.
     *  For a relative TRS R/S, a redex is innermost iff all its strict
     *  subterms are both R-normal forms and S-normal forms.
     */
    INNERMOST(false, "innermost"),
    /** (Max-)parallel-innermost rewriting. All innermost redexes are rewritten
     *  simultaneously. At least one innermost redex is rewritten.
     */
    PARALLEL_INNERMOST(true, "parallel-innermost"),
    /**
     *  Outermost rewriting. Only outermost redexes can be rewritten.
     */
    OUTERMOST(false, "outermost"),
    /**
     *  Parallel simultaneous rewriting. Only interesting in the probabilistic setting.
     *  Multiple redexes can be rewritten simultaneously such that the probabilities are
     *  only used once (and not multiple times for all possible tuples of outcomes).
     */
    PARALLEL_SIMULTANEOUS(true, "parallel-somultaneous"),
    /**
     *  Parallel simultaneous innermost rewriting. Para-Sim rewriting 
     *  but only innermost redexes can be rewritten.
     */
    PARALLEL_SIMULTANEOUS_INNERMOST(true, "parallel-simultaneous-innermost"),
    /**
     *  Parallel simultaneous innermost rewriting. Para-Sim rewriting 
     *  but only outermost redexes can be rewritten.
     */
    PARALLEL_SIMULTANEOUS_OUTERMOST(true, "parallel-iomultaneous-outermost");

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
    private RewriteStrategy(boolean contractsMultipleRedexes, String representation) {
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
