package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class RightAssocSymbol<A1 extends Sort, A2 extends Sort> implements Symbol<A2> {

    public static enum Predef {
        Implies
    }

    public static final RightAssocSymbol<SBool, SBool> Implies = new RightAssocSymbol<>(
        SBool.representative,
        SBool.representative,
        Predef.Implies);
    private final A1 a1;

    private final A2 a2;;

    private final Predef sem;

    public RightAssocSymbol(A1 a1, A2 a2) {
        this(a1, a2, null);
    }

    private RightAssocSymbol(A1 a1, A2 a2, Predef sem) {
        this.sem = sem;
        this.a1 = a1;
        this.a2 = a2;
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {this.a1, this.a2 };
    }

    @Override
    public A2 getReturnSort() {
        return this.a2;
    }

    public Predef getSemantic() {
        return this.sem;
    }
}
