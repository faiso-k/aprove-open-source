package aprove.input.Programs.SMTLIB.Sorts;

import immutables.*;

/**
 * Represents native sorts. Native Sorts must be Singletons.
 */
public class NativeSort extends AbstractSort implements Immutable {
    public static final NativeSort NATIVESORT = new NativeSort();

    protected NativeSort() {
    }

    /* Assumes that NativeSorts are represented by singleton objects */
    @Override
    public boolean equalsWith(final AbstractSort abstractSort) {
        if (abstractSort instanceof NativeSort) {
            return true;
        } else {
            return false;
        }
    }
}
