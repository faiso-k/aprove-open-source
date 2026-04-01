package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import immutables.*;

/**
 * A binary integer function expression.
 * @author cryingshadow
 * @version $Id$
 */
public interface BinaryIntegerFunctionExpression
extends BinaryArithmeticFunctionExpression, CompoundFunctionalIntegerExpression {

    @Override
    @SuppressWarnings("unchecked")
    default ImmutableList<? extends FunctionalIntegerExpression> getArguments() {
        return (ImmutableList<? extends FunctionalIntegerExpression>)BinaryExpression.getArguments(this);
    }

    @Override
    FunctionalIntegerExpression getLhs();

    @Override
    FunctionalIntegerExpression getRhs();

    @Override
    default SMTExpression<SInt> toSMTExp() {
        SMTExpression<SInt> lhsExp = this.getLhs().toSMTExp();
        SMTExpression<SInt> rhsExp = this.getRhs().toSMTExp();
        switch (this.getOperation()) {
            case ADD:
                return Ints.add(lhsExp, rhsExp);
            case SUB:
                return Ints.subtract(lhsExp, rhsExp);
            case MUL:
                return Ints.times(lhsExp, rhsExp);
            case EIDIV:
                return Ints.div(lhsExp, rhsExp);
            case EMOD:
                return Ints.mod(lhsExp, rhsExp);
            default:
                throw new UnsupportedOperationException("No viable cases left. Operation: " + this.getOperation());
        }
    }

}
