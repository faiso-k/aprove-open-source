package aprove.input.Programs.SMTLIB.Sorts;

import immutables.*;

/**
 * Represents all sorts for the SMT-LIB benchmark.
 */
public abstract class AbstractSort implements Immutable {
    public abstract boolean equalsWith(final AbstractSort abstractSort);
}
