package aprove.input.Programs.SMTLIB.Sorts;

import immutables.*;

/**
 * Represents boolean sort.
 */
public class SortBool extends NativeSort implements Immutable {
    public static SortBool SORTBOOL = new SortBool();

    private SortBool() {
    }

    /* Assumes that NativeSorts are represented by singleton objects */
    @Override
    public boolean equalsWith(final AbstractSort abstractSort) {
        return this == abstractSort;
    }
}
