package aprove.verification.oldframework.SMT.Expressions.Sorts;

import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class SBool extends Sort {

    public static final SBool representative = new SBool();

    private SBool() {
    }

    @Override
    public Symbol0<SBool> createVariable(final String name) {
        return new NamedSymbol0<>(SBool.representative, name);
    }

    @Override
    public Symbol0<SBool> createVariable() {
        return new Symbol0<>(SBool.representative);
    }

    @Override
    public Class<Boolean> getRepresentingClass() {
        return Boolean.class;
    }

    @Override
    public String toString() {
        return "Bool";
    }
}
