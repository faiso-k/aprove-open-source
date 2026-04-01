package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class Symbol3<S extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> implements Symbol<S> {

    public static enum Predef {
        // Core Theory
        ITE
    }

    public static final Symbol3<Sort, SBool, Sort, Sort> ITE = new Symbol3<>(
        Sort.representative,
        SBool.representative,
        Sort.representative,
        Sort.representative,
        Predef.ITE);

    private final A0 a0;
    private final A1 a1;
    private final A2 a2;
    private final S rv;
    private final Predef sem;

    public Symbol3(S rv, A0 a0, A1 a1, A2 a2) {
        this(rv, a0, a1, a2, null);
    }

    private Symbol3(S rv, A0 a0, A1 a1, A2 a2, Predef sem) {
        this.rv = rv;
        this.a0 = a0;
        this.a1 = a1;
        this.a2 = a2;
        this.sem = sem;
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {this.a0, this.a1, this.a2 };
    }

    @Override
    public S getReturnSort() {
        return this.rv;
    }

    public Predef getSemantic() {
        return this.sem;
    }

}
