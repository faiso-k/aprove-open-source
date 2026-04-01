package aprove.input.Programs.SMTLIB.Sorts;

import java.util.*;

import aprove.*;
import aprove.input.Programs.SMTLIB.Terms.*;

/**
 * Represents all function sorts.
 */
public abstract class AbstractFunctionSort extends AbstractSort {
    private final NativeSort to;

    public AbstractFunctionSort(final NativeSort to) {
        if (Globals.useAssertions) {
            assert to != null;
        }
        this.to = to;
    }

    /**
     * Checks if all terms (arguments) have the same sort as the function
     * declaration.
     * @param terms The arguments
     * @return
     */
    public abstract boolean checkSort(List<SMTTermWrapper> terms);

    public NativeSort getTo() {
        return this.to;
    }

}
