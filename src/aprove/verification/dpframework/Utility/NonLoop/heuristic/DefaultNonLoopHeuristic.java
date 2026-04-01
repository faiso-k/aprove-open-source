package aprove.verification.dpframework.Utility.NonLoop.heuristic;
/**
 *
 * @author Tim Enger
 */

public class DefaultNonLoopHeuristic implements NonLoopHeurisitic {

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean forwardNarrowing() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean backwardNarrowing() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean allowVarPos() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int maximumIterations() {
        return 2500;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int narrowingSteps() {
        return 3;
    }

}

