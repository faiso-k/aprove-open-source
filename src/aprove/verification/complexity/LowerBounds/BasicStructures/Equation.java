package aprove.verification.complexity.LowerBounds.BasicStructures;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;


public class Equation extends Relation<TRSFunctionApplication, TRSFunctionApplication, Equation> {

    public Equation(TRSFunctionApplication lhs, TRSFunctionApplication rhs) {
        super(lhs, rhs);
    }

    public FunctionSymbol getLeftRootSymbol() {
        return this.lhs.getRootSymbol();
    }

    public FunctionSymbol getRightRootSymbol() {
        return this.rhs.getRootSymbol();
    }

    @Override
    Equation cloneWith(TRSFunctionApplication lhs, TRSFunctionApplication rhs) {
        return new Equation(lhs, rhs);
    }

    @Override
    String getSymbol(Export_Util eu) {
        return eu.equivalent();
    }

}
