package aprove.verification.complexity.TruthValue;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Class for singleton complexity classes.
 *
 * Only instances should be the constants in {@link ComplexityValue}.
 */
public abstract class SingletonComplexity extends ComplexityValue {

    private final String text;

    protected SingletonComplexity(Order order, Optional<MinMaxExpr> concreteValue, String text) {
        super(order, concreteValue);
        this.text = text;
    }

    protected SingletonComplexity(Order order, Optional<MinMaxExpr> concreteValue) {
        this(order, concreteValue, order.toString());
    }

    @Override
    public YNM fallbackToYNM() {
        return this.order.fallback;
    }

    public boolean isCompletelyKnown() {
        return this.order.fallback != YNM.MAYBE;
    }

    @Override
    public String export(Export_Util eu) {
        return text;
    }

}
