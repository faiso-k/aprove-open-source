package aprove.verification.oldframework.IntegerReasoning.octagondomain.dbm;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

public class DBMPosition implements Comparable<DBMPosition> {

    static DBMPosition createNegatedPosition(final IntegerVariable variable, final int listIndex) {
        assert listIndex % 2 == 1;
        return new DBMPosition(variable, true, listIndex);
    }

    static DBMPosition createPosition(final IntegerVariable variable, final int listIndex) {
        assert listIndex % 2 == 0;
        return new DBMPosition(variable, false, listIndex);
    }

    private static int hashCode(final IntegerVariable variable, final boolean negated) {
        final int prime = 31;
        int result = 1;
        result = prime * result + (negated ? 1231 : 1237);
        result = prime * result + ((variable == null) ? 0 : variable.hashCode());
        return result;
    }

    private final int hashCode;

    private final int listIndex;

    private final boolean negated;

    private final IntegerVariable variable;

    private DBMPosition(IntegerVariable variable, boolean negated, int listIndex) {
        this.variable = variable;
        this.negated = negated;
        this.hashCode = DBMPosition.hashCode(variable, negated);
        this.listIndex = listIndex;
    }

    @Override
    public int compareTo(final DBMPosition other) {
        final String thisVarString = this.variable.toString();
        final String otherVarString = other.variable.toString();

        final int stringComparison = thisVarString.compareTo(otherVarString);
        if (stringComparison != 0) {
            return stringComparison;
        } else {
            /* Both represent the same variables. We want the positive
             * versions to come before the negated versions */
            if (this.negated == other.negated) {
                return 0;
            } else if (other.negated) {
                return -1;
            } else {
                return 1;
            }
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof DBMPosition)) {
            return false;
        }
        final DBMPosition other = (DBMPosition) obj;
        if (this.negated != other.negated) {
            return false;
        }
        if (this.variable == null) {
            if (other.variable != null) {
                return false;
            }
        } else if (!this.variable.equals(other.variable)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String toString() {
        final StringBuilder stringBuilder = new StringBuilder("DBMPosition: ");
        if (this.negated) {
            stringBuilder.append("-");
        }
        stringBuilder.append(this.variable.toString());
        return stringBuilder.toString();
    }

    int getListIndex() {
        return this.listIndex;
    }

    /**
     * @return If this is a positive position, then return the corresponding
     * negative position, and vice versa.
     */
    DBMPosition getNegatedPosition() {
        final int newListIndex;
        if (this.negated) {
            newListIndex = this.listIndex - 1;
        } else {
            newListIndex = this.listIndex + 1;
        }
        return new DBMPosition(this.variable, !this.negated, newListIndex);
    }

    IntegerVariable getVariable() {
        return this.variable;
    }

    /**
     * Either this or isPositiveEntryId(id) is always true, but never both
     * @return True iff this position is associated with a negative variable
     */
    boolean isNegativeEntryId() {
        return this.negated;
    }

    /**
     * Either this or isNegativeEntryId(id) is always true, but never both
     * @return True iff this position is associated with a positive variable
     */
    boolean isPositiveEntryId() {
        return !this.negated;
    }

    /**
     * @return An expression that denotes the variable this position represents. If this position represents a negated
     *         variable, the expression denotes the negated variable as well.
     */
    FunctionalIntegerExpression toIntegerExpression() {
        if (this.negated) {
            return this.variable.negate();
        } else {
            return this.variable;
        }
    }

}
