package aprove.verification.oldframework.SMT.Expressions.Sorts;

import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class Sort {
    public static final Sort representative = new Sort();

    protected Sort() {
    }

    public Symbol0<?> createVariable(final String name) {
        throw new RuntimeException("Sort is only a helper for polymorphic smt-lib functions and no real sort.");
    }

    public Class<?> getRepresentingClass() {
        return Sort.class;
    }

    public Symbol0 createVariable() {
        throw new RuntimeException("Sort is only a helper for polymorphic smt-lib functions and no real sort.");
    }
}
