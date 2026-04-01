package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class ChainableSymbol<A0 extends Sort> implements Symbol<SBool> {
    public static enum Predef {
        Equivalent, IntsGreater, IntsGreaterEqual, IntsLess, IntsLessEqual
    }

    public static final ChainableSymbol<Sort> Equivalent =
        new ChainableSymbol<>(Sort.representative, Predef.Equivalent);

    public static final ChainableSymbol<SInt> IntsGreater = new ChainableSymbol<>(
        SInt.representative,
        Predef.IntsGreater);

    public static final ChainableSymbol<SInt> IntsGreaterEqual = new ChainableSymbol<>(
        SInt.representative,
        Predef.IntsGreaterEqual);

    public static final ChainableSymbol<SInt> IntsLess = new ChainableSymbol<>(SInt.representative, Predef.IntsLess);
    public static final ChainableSymbol<SInt> IntsLessEqual = new ChainableSymbol<>(
        SInt.representative,
        Predef.IntsLessEqual);
    private final A0 a0;
    private final Predef sem;

    public ChainableSymbol(A0 a0) {
        this(a0, null);
    }

    private ChainableSymbol(A0 a0, Predef sem) {
        this.sem = sem;
        this.a0 = a0;
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {this.a0, this.a0 };
    }

    @Override
    public SBool getReturnSort() {
        return SBool.representative;
    }

    public Predef getSemantic() {
        return this.sem;
    }

}
