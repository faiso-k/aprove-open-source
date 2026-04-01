package aprove.input.Programs.SMTLIB.Sorts;

import java.util.*;

import aprove.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import immutables.*;

/**
 * Represents a function sort with constant arity.
 */
public class FunctionSort extends AbstractFunctionSort implements Immutable {
    private final ImmutableArrayList<NativeSort> from;

    private FunctionSort(final NativeSort to,
            final ImmutableArrayList<NativeSort> from) {
        super(to);
        if (Globals.useAssertions) {
            assert from != null;
        }
        this.from = from;
    }

    public static FunctionSort create(final NativeSort to,
        final ArrayList<NativeSort> from) {
        ImmutableArrayList<NativeSort> fromArr = null;
        if (from != null) {
            fromArr = ImmutableCreator.create(from);
        } else {
            fromArr = ImmutableCreator.create(new ArrayList<NativeSort>());
        }
        return new FunctionSort(to, fromArr);
    }

    public static FunctionSort create(final NativeSort to, final NativeSort... from) {
        final ArrayList<NativeSort> fromArr = new ArrayList<NativeSort>();
        for (int i = 0; i < from.length; ++i) {
            fromArr.add(from[i]);
        }
        return new FunctionSort(to, ImmutableCreator.create(fromArr));
    }

    public ImmutableArrayList<NativeSort> getFrom() {
        return this.from;
    }

    @Override
    public boolean checkSort(final List<SMTTermWrapper> terms) {
        if (terms == null) {
            return this.from.size() == 0;
        }

        int i = 0;
        for (final SMTTermWrapper term : terms) {
            if (i + 1 > this.from.size()
                || !this.from.get(i).equalsWith((term.getSort()))) {
                return false;
            }
            i++;
        }
        if (i < this.from.size()) {
            return false;
        }
        return true;
    }

    @Override
    public boolean equalsWith(final AbstractSort abstractSort) {
        if (abstractSort instanceof FunctionSort) {
            final FunctionSort fs = (FunctionSort) abstractSort;
            if (this.getTo().equalsWith(fs.getTo())
                && this.from.size() == fs.from.size()) {
                int i = 0;
                for (final NativeSort ns : this.from) {
                    if (!ns.equals(fs.from.get(i))) {
                        return false;
                    } else {
                        i++;
                    }
                }
                return true;
            }
        }
        return this.from.size() == 0 && this.getTo().equals(abstractSort);
    }
}
