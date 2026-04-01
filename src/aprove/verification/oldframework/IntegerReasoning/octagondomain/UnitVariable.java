package aprove.verification.oldframework.IntegerReasoning.octagondomain;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

public class UnitVariable {

    public static UnitVariable createNegatedVariable(final IntegerVariable variable) {
        return new UnitVariable(variable, true);
    }

    public static UnitVariable createVariable(final IntegerVariable variable) {
        return new UnitVariable(variable, false);
    }

    private final boolean isNegated;

    private final IntegerVariable variable;

    private UnitVariable(final IntegerVariable variable, final boolean isNegated) {
        this.variable = variable;
        this.isNegated = isNegated;
    }

    public IntegerVariable getVariable() {
        return this.variable;
    }

    public boolean isNegated() {
        return this.isNegated;
    }

}
