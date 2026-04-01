package aprove.verification.oldframework.IntegerReasoning.octagondomain;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

public class UnitVariableAnalyzer extends FunctionalIntegerExpressionVisitor {

    private BigInteger coefficient;

    private TraversalState traversalState;

    private IntegerVariable variable;

    public UnitVariable analyze(final FunctionalIntegerExpression expression) {
        this.traversalState = TraversalState.START;
        this.coefficient = BigInteger.ONE;
        this.variable = null;
        this.visit(expression);
        if (this.traversalState.equals(TraversalState.ACCEPT)) {
            if (this.coefficient.equals(BigInteger.ONE)) {
                return UnitVariable.createVariable(this.variable);
            } else {
                assert this.coefficient.equals(BigInteger.valueOf(-1));
                return UnitVariable.createNegatedVariable(this.variable);
            }
        } else {
            return null;
        }
    }

    @Override
    public String toString() {
        final StringBuilder stringBuilder = new StringBuilder("UnitVariableAnalyzer[");
        stringBuilder.append("TraversalState=");
        stringBuilder.append(this.traversalState.toString());
        if (this.traversalState.equals(TraversalState.ACCEPT)) {
            stringBuilder.append(",Variable=");
            stringBuilder.append(this.variable.toString());
            stringBuilder.append(",Coefficient=");
            stringBuilder.append(this.coefficient.toString());
        }
        stringBuilder.append("]");
        return stringBuilder.toString();
    }

    @Override
    public boolean visitAdditionPreorder(final CompoundFunctionalIntegerExpression addition) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitConjunctionPreorder(final CompoundFunctionalIntegerExpression conjunction) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitConstRef(final IntegerConstant constRef) {
        if (
            !(
                this.traversalState.equals(TraversalState.EXPECTVARANDCONST)
                || this.traversalState.equals(TraversalState.FOUNDCONST)
            )
        ) {
            this.coefficient = null;
            this.variable = null;
            // If we do not expect a const ref, stop traversal
            return false;
        }
        final BigInteger value = constRef.getIntegerValue();
        if (value.compareTo(BigInteger.valueOf(1)) == 0) {
            // The coefficient is unit, we do not need to change our standard value
        } else if (value.compareTo(BigInteger.valueOf(-1)) == 0) {
            this.coefficient = this.coefficient.negate();
        } else {
            this.traversalState = TraversalState.REJECT;
            this.coefficient = null;
            return false;
        }
        if (this.traversalState.equals(TraversalState.EXPECTVARANDCONST)) {
            this.traversalState = TraversalState.FOUNDCONST;
            return true;
        } else if (this.traversalState.equals(TraversalState.FOUNDVAR)) {
            this.traversalState = TraversalState.ACCEPT;
            return true;
        } else {
            this.traversalState = TraversalState.REJECT;
            return false;
        }
    }

    @Override
    public boolean visitDisjunctionPreorder(final CompoundFunctionalIntegerExpression disjunction) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitDivisionPreorder(final CompoundFunctionalIntegerExpression division) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitModuloPreorder(CompoundFunctionalIntegerExpression exp) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitMultiplicationPreorder(final CompoundFunctionalIntegerExpression multiplication) {
        if (this.traversalState.equals(TraversalState.START)) {
            this.traversalState = TraversalState.EXPECTVARANDCONST;
            return true;
        } else {
            this.traversalState = TraversalState.REJECT;
            return false;
        }
    }

    @Override
    public boolean visitNegationPreorder(final CompoundFunctionalIntegerExpression negation) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitPowerPreorder(final CompoundFunctionalIntegerExpression power) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitRemainderPreorder(final CompoundFunctionalIntegerExpression remainder) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitShiftLeftPreorder(final CompoundFunctionalIntegerExpression shift) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitShiftRightPreorder(final CompoundFunctionalIntegerExpression shift) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitSubtractionPreorder(final CompoundFunctionalIntegerExpression subtraction) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitUnsignedShiftRightPreorder(final CompoundFunctionalIntegerExpression shift) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    @Override
    public boolean visitVarRef(final IntegerVariable varRef) {
        if (this.traversalState.equals(TraversalState.START)) {
            this.traversalState = TraversalState.ACCEPT;
            this.variable = varRef;
            return true;
        } else if (this.traversalState.equals(TraversalState.EXPECTVARANDCONST)) {
            this.traversalState = TraversalState.FOUNDVAR;
            this.variable = varRef;
            return true;
        } else if (this.traversalState.equals(TraversalState.FOUNDCONST)) {
            this.traversalState = TraversalState.ACCEPT;
            this.variable = varRef;
            return true;
        } else {
            this.traversalState = TraversalState.REJECT;
            return false;
        }
    }

    @Override
    public boolean visitXorPreorder(final CompoundFunctionalIntegerExpression xor) {
        this.traversalState = TraversalState.REJECT;
        return false;
    }

    private enum TraversalState {
        ACCEPT, EXPECTVARANDCONST, FOUNDCONST, FOUNDVAR, REJECT, START
    }

}
