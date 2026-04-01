package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class NamedSymbol2<S extends Sort, A0 extends Sort, A1 extends Sort> extends Symbol2<S, A0, A1> implements NamedSymbol<S> {

    private final String name;

    public NamedSymbol2(S rv, A0 a0, A1 a1, String name) {
        super(rv, a0, a1);
        this.name = name;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public String toString() {
        return this.name + "_2";
    }

}
