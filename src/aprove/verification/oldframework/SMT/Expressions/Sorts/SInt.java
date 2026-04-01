package aprove.verification.oldframework.SMT.Expressions.Sorts;

import java.math.*;

import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class SInt extends Sort {
    public static final SInt representative = new SInt();

    private SInt() {
    }

    @Override
    public NamedSymbol0<SInt> createVariable(final String name) {
        return new NamedSymbol0<>(SInt.representative, name);
    }

    @Override
    public Symbol0<SInt> createVariable() {
        return new Symbol0<>(SInt.representative);
    }

    @Override
    public Class<BigInteger> getRepresentingClass() {
        return BigInteger.class;
    }

    @Override
    public String toString() {
        return "Int";
    }
}
