package aprove.verification.oldframework.IntegerReasoning.utils.additionboundinference;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.utils.intervals.*;

/**
 * Models a relation of the form (-)x + (-)y <= c, for some variables x and y and a
 * constant c. We furthermore only model the cases where x != y. If x = y, the
 * relation can be better modeled using an {@link IntervalEvaluation}.
 *
 * @author Alexander Weinert
 */
public class UnitAdditionBound {
    public static class Builder {
        private IntegerVariable lhsVariable = null, rhsVariable = null;
        private boolean lhsVariableNegated = false, rhsVariableNegated = false;
        private BigInteger bound = null;

        public Builder addVariable(final IntegerVariable variable) {
            assert this.lhsVariable == null || this.rhsVariable == null;

            if (this.lhsVariable == null) {
                this.lhsVariable = variable;
            } else {
                this.rhsVariable = variable;
            }
            return this;
        }

        public Builder addNegatedVariable(final IntegerVariable variable) {
            assert this.lhsVariable == null || this.rhsVariable == null;

            if (this.lhsVariable == null) {
                this.lhsVariable = variable;
                this.lhsVariableNegated = true;
            } else {
                this.rhsVariable = variable;
                this.rhsVariableNegated = true;
            }
            return this;
        }

        public Builder setBound(final BigInteger bound) {
            this.bound = bound;
            return this;
        }

        public UnitAdditionBound build() {
            assert this.lhsVariable != null;
            assert this.rhsVariable != null;
            assert this.bound != null;
            return new UnitAdditionBound(
                this.lhsVariable,
                this.lhsVariableNegated,
                this.rhsVariable,
                this.rhsVariableNegated,
                this.bound);
        }
    }

    private final IntegerVariable lhsVariable;
    private final boolean lhsVariableNegated;
    private final IntegerVariable rhsVariable;
    private final boolean rhsVariableNegated;
    private final BigInteger bound;

    private UnitAdditionBound(
        final IntegerVariable lhsVariable,
        final boolean lhsVariableNegated,
        final IntegerVariable rhsVariable,
        final boolean rhsVariableNegated,
        final BigInteger bound)
    {
        this.lhsVariable = lhsVariable;
        this.lhsVariableNegated = lhsVariableNegated;
        this.rhsVariable = rhsVariable;
        this.rhsVariableNegated = rhsVariableNegated;
        this.bound = bound;
    }

    public IntegerVariable getLhsVariable() {
        return this.lhsVariable;
    }

    public boolean isLhsVariableNegated() {
        return this.lhsVariableNegated;
    }

    public IntegerVariable getRhsVariable() {
        return this.rhsVariable;
    }

    public boolean isRhsVariableNegated() {
        return this.rhsVariableNegated;
    }

    public BigInteger getBound() {
        return this.bound;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.bound == null) ? 0 : this.bound.hashCode());
        result = prime * result + ((this.lhsVariable == null) ? 0 : this.lhsVariable.hashCode());
        result = prime * result + (this.lhsVariableNegated ? 1231 : 1237);
        result = prime * result + ((this.rhsVariable == null) ? 0 : this.rhsVariable.hashCode());
        result = prime * result + (this.rhsVariableNegated ? 1231 : 1237);
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof UnitAdditionBound)) {
            return false;
        }
        final UnitAdditionBound other = (UnitAdditionBound) obj;
        if (this.bound == null) {
            if (other.bound != null) {
                return false;
            }
        } else if (!this.bound.equals(other.bound)) {
            return false;
        }
        if (this.lhsVariable == null) {
            if (other.lhsVariable != null) {
                return false;
            }
        } else if (!this.lhsVariable.equals(other.lhsVariable)) {
            return false;
        }
        if (this.lhsVariableNegated != other.lhsVariableNegated) {
            return false;
        }
        if (this.rhsVariable == null) {
            if (other.rhsVariable != null) {
                return false;
            }
        } else if (!this.rhsVariable.equals(other.rhsVariable)) {
            return false;
        }
        if (this.rhsVariableNegated != other.rhsVariableNegated) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        final StringBuilder stringBuilder = new StringBuilder();
        if (this.lhsVariableNegated) {
            stringBuilder.append("(-");
        }
        stringBuilder.append(this.lhsVariable.toString());
        if (this.lhsVariableNegated) {
            stringBuilder.append(")");
        }
        stringBuilder.append(" + ");
        if (this.rhsVariableNegated) {
            stringBuilder.append("(-");
        }
        stringBuilder.append(this.rhsVariable.toString());
        if (this.rhsVariableNegated) {
            stringBuilder.append(")");
        }
        stringBuilder.append(" <= ");
        stringBuilder.append(this.bound);
        return stringBuilder.toString();
    }

}
