package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class Symbol0<S extends Sort> extends SMTExpression<S> implements Symbol<S> {

    public static enum Predef {
        False, True
    }

    public static final Symbol0<SBool> False = new Symbol0<>(SBool.representative, Predef.False);
    public static final Symbol0<SBool> True = new Symbol0<>(SBool.representative, Predef.True);

    private final Predef sem;

    public Symbol0(S rv) {
        this(rv, null);
    }

    private Symbol0(S rv, Predef sem) {
        super(rv);
        this.sem = sem;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Sort[] getArgumentSorts() {
        return new Sort[] {};
    }

    @Override
    public S getReturnSort() {
        return this.getType();
    }

    public Predef getSemantic() {
        return this.sem;
    }
}
