package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class Symbol2<S extends Sort, A0 extends Sort, A1 extends Sort> implements Symbol<S> {

    public static enum Predef {
        IntsMod
    }

    // Core Theory Symbols

    /**
     * Modulo (for Euclidean integer division - beware that this is different to most programming languages, which use
     * truncating division).
     */
    public static final Symbol2<SInt, SInt, SInt> IntsMod =
        new Symbol2<SInt, SInt, SInt>(
            SInt.representative,
            SInt.representative,
            SInt.representative,
            Predef.IntsMod
        );

    private final A0 a0;

    private final A1 a1;

    private final S rv;

    private final Predef sem;

    public Symbol2(S rv, A0 a0, A1 a1) {
        this(rv, a0, a1, null);
    }

    protected Symbol2(S rv, A0 a0, A1 a1, Predef sem) {
        this.rv = rv;
        this.a0 = a0;
        this.a1 = a1;
        this.sem = sem;
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {this.a0, this.a1 };
    }

    @Override
    public S getReturnSort() {
        return this.rv;
    }

    public Predef getSemantic() {
        return this.sem;
    }

}
