package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class PairwiseSymbol<A0 extends Sort> implements Symbol<SBool> {

    public static enum Predef {
        Distinct
    }

    public static final PairwiseSymbol<Sort> Distinct = new PairwiseSymbol<>(Sort.representative, Predef.Distinct);

    private final A0 a0;

    private final Predef sem;

    public PairwiseSymbol(A0 a0) {
        this(a0, null);
    }

    private PairwiseSymbol(A0 a0, Predef sem) {
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
