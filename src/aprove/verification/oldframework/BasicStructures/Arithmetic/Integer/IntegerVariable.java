package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;

/**
 * An integer variable allows export as SMT expression.
 * @author cryingshadow
 * @version $Id$
 */
public interface IntegerVariable extends Variable, FunctionalIntegerExpression {

    @Override
    default SMTExpression<SInt> toSMTExp() {
        return Ints.intVar(this.getName());
    }

    @Override
    @SuppressWarnings("unchecked")
    default Set<? extends IntegerVariable> getVariables() {
        return (Set<? extends IntegerVariable>)Variable.getVariables(this);
    }

}
