package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class LeftAssocSymbol<A1 extends Sort, A2 extends Sort> implements Symbol<A1> {

    public static enum Predef {
        And, IntsAdd, IntsDiv, IntsSubtract, IntsTimes, Or, Xor

    }

    // Ints Theory Symbols
    public static final LeftAssocSymbol<SBool, SBool> And = new LeftAssocSymbol<>(
        SBool.representative,
        SBool.representative,
        Predef.And);
    public static final LeftAssocSymbol<SInt, SInt> IntsAdd = new LeftAssocSymbol<>(
        SInt.representative,
        SInt.representative,
        Predef.IntsAdd);

    public static final LeftAssocSymbol<SInt, SInt> IntsDiv = new LeftAssocSymbol<>(
        SInt.representative,
        SInt.representative,
        Predef.IntsDiv);

    public static final LeftAssocSymbol<SInt, SInt> IntsSubtract = new LeftAssocSymbol<>(
        SInt.representative,
        SInt.representative,
        Predef.IntsSubtract);

    public static final LeftAssocSymbol<SInt, SInt> IntsTimes = new LeftAssocSymbol<>(
        SInt.representative,
        SInt.representative,
        Predef.IntsTimes);

    public static final LeftAssocSymbol<SBool, SBool> Or = new LeftAssocSymbol<>(
        SBool.representative,
        SBool.representative,
        Predef.Or);
    public static final LeftAssocSymbol<SBool, SBool> Xor = new LeftAssocSymbol<>(
        SBool.representative,
        SBool.representative,
        Predef.Xor);
    private final A1 a1;
    private final A2 a2;
    private final Predef sem;

    public LeftAssocSymbol(A1 a1, A2 a2) {
        this(a1, a2, null);
    }

    private LeftAssocSymbol(A1 a1, A2 a2, Predef sem) {
        this.sem = sem;
        this.a1 = a1;
        this.a2 = a2;
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {this.a1, this.a2 };
    }

    @Override
    public A1 getReturnSort() {
        return this.a1;
    }

    public Predef getSemantic() {
        return this.sem;
    }
}
