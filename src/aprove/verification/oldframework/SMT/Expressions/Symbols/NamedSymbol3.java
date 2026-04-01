package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class NamedSymbol3<S extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> extends Symbol3<S, A0, A1, A2> implements NamedSymbol<S> {

    private final String name;

    public NamedSymbol3(S rv, A0 a0, A1 a1, A2 a2, String name) {
        super(rv, a0, a1, a2);
        this.name = name;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public String toString() {
        return this.name + "_3";
    }

}
