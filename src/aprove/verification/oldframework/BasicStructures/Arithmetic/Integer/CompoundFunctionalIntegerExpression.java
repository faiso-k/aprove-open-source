package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import immutables.*;

/**
 * A compound functional integer expression.
 * @author cryingshadow
 * @version $Id$
 */
public interface CompoundFunctionalIntegerExpression extends CompoundExpression, IntegerFunctionExpression {

    @Override
    ImmutableList<? extends FunctionalIntegerExpression> getArguments();

    @Override
    default String getName() {
        return this.getOperation().getName();
    }

    /**
     * @return The arithmetic operation of this.
     */
    ArithmeticOperationType getOperation();

    @Override
    default FunctionSymbol getRootSymbol() {
        return this.getOperation().getRootSymbol();
    }

    @Override
    @SuppressWarnings("unchecked")
    default Set<? extends IntegerVariable> getVariables() {
        return (Set<? extends IntegerVariable>)CompoundExpression.getVariables(this);
    }

}
