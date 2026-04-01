package aprove.verification.dpframework.Utility.NonLoop.heuristic;
/**
 *
 * @author Tim Enger
 */

public class PassedNonLoopHeuristic implements NonLoopHeurisitic {

    /**
     * Number of narrowings steps in pre-processing
     */
    private final int narrowing;

    /**
     * Flag to indicate if forward narrowing should be used
     */
    private final boolean forwardNarrowing;

    /**
     * Flag to indicate if backward narrowing should be used
     */
    private final boolean backwardNarrowing;

    /**
     * Flag to indicate if narrowing into variables is permitted
     */
    private final boolean allowVarPos;

    /**
     * The maximum number of iterations done at the moment.
     */
    private final int maxIterations;

    /**
     * Constructor
     *
     * @param narrowingArg
     *            Number of narrowings steps in pre-processing
     * @param forwardNarrowingArg
     *            Flag to indicate if forward narrowing should be used
     * @param backwardNarrowingArg
     *            Flag to indicate if backward narrowing should be used
     * @param allowVarPosArg
     *            Flag to indicate if narrowing into variables is permitted
     * @param maxIterationsArg
     *            The maximum number of iterations done at the moment.
     */
    public PassedNonLoopHeuristic(final int narrowingArg, final boolean forwardNarrowingArg,
            final boolean backwardNarrowingArg, final boolean allowVarPosArg, final int maxIterationsArg) {
        this.narrowing = narrowingArg;
        this.forwardNarrowing = forwardNarrowingArg;
        this.backwardNarrowing = backwardNarrowingArg;
        this.allowVarPos = allowVarPosArg;
        this.maxIterations = maxIterationsArg;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean forwardNarrowing() {
        return this.forwardNarrowing;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean backwardNarrowing() {
        return this.backwardNarrowing;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean allowVarPos() {
        return this.allowVarPos;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int maximumIterations() {
        return this.maxIterations;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int narrowingSteps() {
        return this.narrowing;
    }

}

