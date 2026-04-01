package aprove.verification.dpframework.Utility.NonLoop.heuristic;

/**
 * Heuristic for Nonloop-Processor.
 *
 * @author Tim Enger
 */

public interface NonLoopHeurisitic {

    /**
     * @return <tt>True</tt> if forward narrowing should be done.
     */
    boolean forwardNarrowing();

    /**
     * @return <tt>True</tt> if backward narrowing should be done.
     */
    boolean backwardNarrowing();

    /**
     * @return <tt>True</tt> if narrowing into variable postions is allowed.
     */
    boolean allowVarPos();

    /**
     * @return The maximum number of iterations.
     */
    int maximumIterations();

    /**
     * @return The number of narrowings steps done in the pre processing.
     */
    int narrowingSteps();
}
