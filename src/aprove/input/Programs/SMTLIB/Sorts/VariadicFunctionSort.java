package aprove.input.Programs.SMTLIB.Sorts;

import java.util.*;

import aprove.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import immutables.*;

/**
 * Represents a function sort with variable (but with a minimum) arity.
 */
public class VariadicFunctionSort extends AbstractFunctionSort implements
        Immutable {
    private final int minimalArity;
    private final NativeSort from;

    private VariadicFunctionSort(final NativeSort to, final NativeSort from,
            final int minArity) {
        super(to);

        if (Globals.useAssertions) {
            assert to != null;
            assert from != null;
            assert minArity >= 1;
        }

        this.from = from;
        this.minimalArity = minArity;
    }

    public static VariadicFunctionSort create(final NativeSort to,
        final NativeSort from,
        final int minArity) {
        return new VariadicFunctionSort(to, from, minArity);
    }

    public NativeSort getFrom() {
        return this.from;
    }

    public int getMinimalArity() {
        return this.minimalArity;
    }

    @Override
    public boolean checkSort(final List<SMTTermWrapper> terms) {
        if (terms == null || terms.size() < this.minimalArity) {
            return false;
        }

        for (final SMTTermWrapper tw : terms) {
            if (!this.from.equalsWith(tw.getSort())) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equalsWith(final AbstractSort abstractSort) {
        if (abstractSort instanceof VariadicFunctionSort) {
            final VariadicFunctionSort fs = (VariadicFunctionSort) abstractSort;
            return this.getTo().equalsWith(fs.getTo())
                && this.minimalArity == fs.minimalArity
                && this.from.equalsWith(fs.from);
        }
        return false;
    }

}
