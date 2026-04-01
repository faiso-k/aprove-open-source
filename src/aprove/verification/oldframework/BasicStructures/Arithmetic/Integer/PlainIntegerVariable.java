package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;

/**
 * Plain integer variable.
 * @author cryingshadow
 * @version $Id$
 */
public class PlainIntegerVariable extends VariableSkeleton implements IntegerVariable {

    /**
     * @param n The name of the variable.
     */
    public PlainIntegerVariable(String n) {
        super(n);
    }

    @Override
    public boolean equals(Object o) {
        return Variable.equals(this, o);
    }

    @Override
    @SuppressWarnings("unchecked")
    public Set<? extends IntegerVariable> getVariables() {
        return (Set<? extends IntegerVariable>)Variable.getVariables(this);
    }

    @Override
    public int hashCode() {
        return Variable.hashCode(this);
    }

    @Override
    public FunctionalIntegerExpression negate() {
        return new PlainIntegerOperation(ArithmeticOperationType.NEG, this);
    }

    @Override
    public String toString() {
        return this.toPrettyString();
    }

}
