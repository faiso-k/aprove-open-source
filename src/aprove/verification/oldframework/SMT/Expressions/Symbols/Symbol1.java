package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class Symbol1<S extends Sort, A0 extends Sort> implements Symbol<S> {

    public static enum Predef {
        IntsAbs, IntsNegate, Not
    }

    public static final Symbol1<SInt, SInt> IntsAbs = new Symbol1<>(
        SInt.representative,
        SInt.representative,
        Predef.IntsAbs);
    public static final Symbol1<SInt, SInt> IntsNegate = new Symbol1<>(
        SInt.representative,
        SInt.representative,
        Predef.IntsNegate);
    public static final Symbol1<SBool, SBool> Not = new Symbol1<>(
        SBool.representative,
        SBool.representative,
        Predef.Not);

    private final A0 a0;
    private final S rv;
    private final Predef sem;

    public Symbol1(S rv, A0 a0) {
        this(rv, a0, null);
    }

    private Symbol1(S rv, A0 a0, Predef sem) {
        this.rv = rv;
        this.a0 = a0;
        this.sem = sem;
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {this.a0 };
    }

    @Override
    public S getReturnSort() {
        return this.rv;
    }

    public Predef getSemantic() {
        return this.sem;
    }

}
