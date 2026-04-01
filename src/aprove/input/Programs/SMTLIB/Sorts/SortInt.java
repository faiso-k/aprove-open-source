package aprove.input.Programs.SMTLIB.Sorts;

import immutables.*;

/**
 * Represents integer sort.
 */
public class SortInt extends NativeSort implements Immutable {
    public static SortInt SORTINT = new SortInt();

    private SortInt() {
    }

    /* Assumes that NativeSorts are represented by singleton objects */
    @Override
    public boolean equalsWith(final AbstractSort abstractSort) {
        return this == abstractSort;
    }
}
