package aprove.verification.oldframework.Logic;

import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.prooftree.Obligations.*;

/**
 * @author nowonder, azazel
 */
public interface TruthValue {

    public static class CombineException extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }

    /**
     * Returns true if this result cannot be improved anymore
     * (YES or NO for Termination, tight bounds for complexity...).
     *
     * Intuitively, this is quiet similar to {@link TruthValue#isCompletelyKnown()},
     * but {@link ObligationNode#isTruthValueKnown()} expects something different.
     */
    public boolean isOptimal();

    public boolean isCompletelyKnown();

    public boolean isCompletelyUnknown();

    public TruthValue and(TruthValue other);

    public TruthValue or(TruthValue other);

    /**
     * Combines two TruthValues not contradicting themselves into one "more defined" TruthValue.
     *
     * @throws CombineException if combining is not possible
     */
    public TruthValue combine(TruthValue other) throws CombineException;

    public TruthValue not();

    public TruthValue mult(TruthValue other);

    /**
     * Converts an arbitrary TruthValue into a YNM.
     */
    public YNM fallbackToYNM();

    /**
     * docu-guess: Checks if <code>this</code> is less defined then
     * <code>newStatus</code>, i.e. the TruthValue could change to newStatus
     * without conflicting with its old value.
     */
    public boolean canGoTo(TruthValue newStatus);

    /**
     * Returns the truth-value in a format valid for the WST mode
     */
    public String toWstString();

    public default String toBenchmarkResult() {
        return this.toWstString();
    }

    public abstract Color toColor();

}
