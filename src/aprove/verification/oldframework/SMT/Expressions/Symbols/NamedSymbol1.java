package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class NamedSymbol1<S extends Sort, A0 extends Sort> extends Symbol1<S, A0> implements NamedSymbol<S> {

    private final String name;

    public NamedSymbol1(S rv, A0 a0, String name) {
        super(rv, a0);
        this.name = name;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public String toString() {
        return this.name + "_1";
    }

}
